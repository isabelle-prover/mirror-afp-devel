section \<open>Divisibility\<close>

theory Relational_Divisibility

imports Relational_Constructions

begin

text \<open>
This theory gives relational axioms and definitions for divisibility.
We start with the definitions, which are based on standard relational constructions.
Then follow the axioms, which are relational formulations of axioms expressed in predicate logic in \cite{Cegielski1989}.
\<close>

context bounded_distrib_allegory_signature
begin

definition antichain :: "'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "antichain r s \<equiv> vector s \<and> r \<sqinter> s \<sqinter> s\<^sup>T \<le> 1"

end

class divisibility_op =
  fixes divisibility :: 'a ("D")

class divisibility_def = relation_algebra + divisibility_op
begin

text \<open>
\<open>Dbot\<close> is the least element of the divisibility order, which represents the number $1$.
\<close>

definition Dbot :: "'a" where
  "Dbot \<equiv> least D top"

text \<open>
\<open>Datoms\<close> are the atoms of the divisibility order, which represent the prime numbers.
\<close>

definition Datoms :: "'a" where
  "Datoms \<equiv> minimal D (-Dbot)"

text \<open>
\<open>Datoms\<close> are the mono-atomic elements of the divisibility order, which represent the prime powers.
\<close>

definition Dmono :: "'a" where
  "Dmono \<equiv> univalent_part ((D \<sqinter> Datoms)\<^sup>T) * top"

text \<open>
\<open>Dfactor\<close> relates $p$ to $x$ if and only if $p$ is maximal prime power factor of $x$.
\<close>

definition Dfactor :: "'a" where
  "Dfactor \<equiv> maximal D (D \<sqinter> Dmono)"

text \<open>
\<open>Dsupport\<close> relates $x$ to $y$ if and only if $y$ is the product of all primes below $x$.
\<close>

definition Dsupport :: "'a" where
  "Dsupport \<equiv> symmetric_quotient (Datoms \<sqinter> D) Dfactor"

text \<open>
\<open>Dsucc\<close> relates $x$ to $y$ if and only if $y$ is the product of prime power $x$ with its base prime.
\<close>

definition Dsucc :: "'a" where
  "Dsucc \<equiv> greatest D (D \<sqinter> -1)"

text \<open>
\<open>Dinc\<close> relates $x$ to $y$ if and only if $y$ is the product of $x$ with all its base primes.
\<close>

definition Dinc :: "'a" where
  "Dinc \<equiv> symmetric_quotient Dfactor (Dsucc * Dfactor)"

text \<open>
\<open>Datomsbot\<close> includes the number $1$ with the prime numbers.
\<close>

definition Datomsbot :: "'a" where
  "Datomsbot \<equiv> Datoms \<squnion> Dbot"

text \<open>
\<open>Dmonobot\<close> includes the number $1$ with the prime powers.
\<close>

definition Dmonobot :: "'a" where
  "Dmonobot \<equiv> Dmono \<squnion> Dbot"

text \<open>
\<open>Dfactorbot\<close> is like \<open>Dfactor\<close> except it also relates $1$ to $1$.
\<close>

definition Dfactorbot :: "'a" where
  "Dfactorbot \<equiv> maximal D (D \<sqinter> Dmonobot)"

text \<open>
We consider the following axioms for \<open>D\<close>.
They correspond to axioms A1--A3, A6--A9, A11--A13 and A15--A16 of \cite{Cegielski1989}.
\<close>

abbreviation D1_reflexive              :: "'a \<Rightarrow> bool" where "D1_reflexive              _ \<equiv> reflexive D" (* A1 *)
abbreviation D2_antisymmetric          :: "'a \<Rightarrow> bool" where "D2_antisymmetric          _ \<equiv> antisymmetric D" (* A2 *)
abbreviation D3_transitive             :: "'a \<Rightarrow> bool" where "D3_transitive             _ \<equiv> transitive D" (* A3 *)
abbreviation D6_least_surjective       :: "'a \<Rightarrow> bool" where "D6_least_surjective       _ \<equiv> surjective Dbot" (* A6 *)
abbreviation D7_pre_f_decomposable     :: "'a \<Rightarrow> bool" where "D7_pre_f_decomposable     _ \<equiv> supremum D (D \<sqinter> Dmono) = 1" (* A7 *)
abbreviation D8_fibered                :: "'a \<Rightarrow> bool" where "D8_fibered                _ \<equiv> Dmono \<sqinter> D\<^sup>T * (Datoms \<sqinter> D) \<sqinter> Dmono\<^sup>T \<le> D \<squnion> D\<^sup>T" (* A8 *)
abbreviation D9_f_decomposable         :: "'a \<Rightarrow> bool" where "D9_f_decomposable         _ \<equiv> Datoms \<sqinter> D \<le> D * Dfactor" (* A9 *)
abbreviation D11_atomic                :: "'a \<Rightarrow> bool" where "D11_atomic                _ \<equiv> D\<^sup>T * Datoms = -Dbot" (* A11 *)
abbreviation D12_infinite_base         :: "'a \<Rightarrow> bool" where "D12_infinite_base         _ \<equiv> -D\<^sup>T * Datoms = top" (* A12 *)
abbreviation D13_supportable           :: "'a \<Rightarrow> bool" where "D13_supportable           _ \<equiv> total Dsupport" (* A13 *)
abbreviation D15a_discrete_fibers_succ :: "'a \<Rightarrow> bool" where "D15a_discrete_fibers_succ _ \<equiv> Dmono \<le> Dsucc * top" (* A15(1) *)
abbreviation D15b_discrete_fibers_pred :: "'a \<Rightarrow> bool" where "D15b_discrete_fibers_pred _ \<equiv> Dmono \<le> Dsucc\<^sup>T * top" (* A15(2) *)
abbreviation D16_incrementable         :: "'a \<Rightarrow> bool" where "D16_incrementable         _ \<equiv> total Dinc" (* A16 *)

subsection \<open>Partial order\<close>

lemma div_antisymmetric_equal:
  assumes "D1_reflexive _"
      and "D2_antisymmetric _"
    shows "D \<sqinter> D\<^sup>T = 1"
  by (simp add: assms dual_order.antisym reflexive_conv_closed)

lemma div_idempotent:
  assumes "D1_reflexive _"
      and "D3_transitive _"
    shows "idempotent D"
  using assms preorder_idempotent by auto

lemma div_total:
  assumes "D1_reflexive _"
    shows "D * top = top"
  by (simp add: assms reflexive_conv_closed reflexive_mult_closed total_var)

lemma div_surjective:
  assumes "D1_reflexive _"
    shows "top * D = top"
  by (simp add: assms reflexive_conv_closed reflexive_mult_closed surjective_var)

lemma div_below_div_converse:
  assumes "D2_antisymmetric _"
      and "x \<le> D"
    shows "D \<sqinter> x\<^sup>T \<le> x"
  by (smt assms conv_dist_inf conv_involutive coreflexive_symmetric inf.cobounded2 inf.orderE inf_left_commute)

subsection \<open>Bounds\<close>

text \<open>
The least element can be introduced equivalently by
\begin{itemize}
\item defining \<open>Dbot = least D top\<close> and axiomatising either \<open>surjective Dbot\<close> or \<open>Dbot \<noteq> bot\<close>, or
\item axiomatising \<open>point Dbot\<close> and \<open>Dbot \<le> D\<close>.
\end{itemize}
\<close>

lemma div_least_div:
  "Dbot \<le> D"
  by (simp add: Dbot_def compl_le_swap2 least_def top_right_mult_increasing)

lemma div_least_vector:
  "vector Dbot"
  by (simp add: Dbot_def complement_vector least_def mult_assoc)

lemma div_least_injective:
  assumes "D2_antisymmetric _"
    shows "injective Dbot"
  by (metis assms div_least_div div_least_vector antisymmetric_inf_closed inf.absorb2 vector_covector)

lemma div_least_point:
  assumes "D2_antisymmetric _"
      and "D6_least_surjective _"
    shows "point Dbot"
  using assms div_least_injective div_least_vector by blast

lemma div_point_least:
  assumes "D2_antisymmetric _"
      and "point x"
      and "x \<le> D"
    shows "x = least D top"
proof (rule order.antisym)
  show "x \<le> least D top"
    by (smt (verit, ccfv_SIG) assms(2,3) comp_associative double_compl inf_top.left_neutral least_def schroeder_4 vector_covector)
  have 1: "D \<sqinter> x\<^sup>T \<le> x"
    by (smt (verit, best) assms(1,3) conv_dist_inf inf.absorb1 inf.sup_same_context inf_assoc inf_le2 one_inf_conv)
  have "-x = (-x \<sqinter> x\<^sup>T) * top"
    using assms(2) complement_vector surjective_conv_total vector_inf_comp by auto
  also have "... \<le> -D * top"
    using 1 by (simp add: inf.sup_monoid.add_commute mult_left_isotone p_shunting_swap)
  finally show "least D top \<le> x"
    by (simp add: compl_le_swap2 least_def)
qed

lemma div_least_surjective_iff:
  assumes "D2_antisymmetric _"
    shows "D6_least_surjective _ \<longleftrightarrow> (\<exists>x . point x \<and> x \<le> D)"
  using Dbot_def assms div_least_div div_point_least div_least_point by auto

lemma div_least_converse:
  assumes "D2_antisymmetric _"
    shows "D \<sqinter> Dbot\<^sup>T \<le> Dbot"
  using assms div_below_div_converse div_least_div by blast

lemma bot_div_bot:
  assumes "D1_reflexive _"
      and "D3_transitive _"
    shows "D * Dbot = Dbot"
  by (metis assms div_idempotent Dbot_def antisym_conv mult_1_left mult_left_isotone transitive_least)

lemma all_div_bot:
  assumes "D2_antisymmetric _"
      and "D6_least_surjective _"
    shows "D\<^sup>T * Dbot = top"
  using assms div_least_div div_least_point inf.order_eq_iff schroeder_4_p schroeder_6 shunt_bijective by fastforce

lemma div_strict_bot:
  assumes "D2_antisymmetric _"
    shows "(D \<sqinter> -1) * Dbot = bot"
proof -
  have "(D\<^sup>T \<sqinter> -1) * top \<le> -D * top"
    using assms inf_commute mult_left_isotone p_shunting_swap by force
  thus ?thesis
    by (smt (verit, ccfv_threshold) Dbot_def conv_complement conv_dist_comp conv_dist_inf conv_involutive equivalence_one_closed inf_p inf_top.left_neutral le_bot least_def regular_in_p_image_iff schroeder_6)
qed

subsection \<open>Atoms\<close>

text \<open>
The atoms can be introduced equivalently by
\begin{itemize}
\item defining \<open>Datoms = minimal D (-Dbot)\<close> and axiomatising either \<open>D\<^sup>T * Datoms = -Dbot\<close> or \<open>-Dbot \<le> D\<^sup>T * Datoms\<close> or \<open>-D \<le> D\<^sup>T * Datoms\<close>, or
\item axiomatising \<open>antichain D Datoms\<close> and \<open>D\<^sup>T * Datoms = -Dbot\<close>.
\end{itemize}
\<close>

lemma div_atoms_vector:
  "vector Datoms"
  by (simp add: Datoms_def div_least_vector comp_associative minimal_def vector_complement_closed vector_inf_closed)

lemma div_atoms_bot_vector:
  "vector Datomsbot"
  by (simp add: div_atoms_vector Datomsbot_def div_least_vector mult_right_dist_sup)

lemma div_least_not_atom:
  "Dbot \<le> -Datoms"
  by (simp add: Datoms_def minimal_def)

lemma div_atoms_antichain:
  "antichain D Datoms"
proof (unfold antichain_def, rule conjI, fact div_atoms_vector)
  have "(D \<sqinter> -1) * Datoms \<le> (D \<sqinter> -1) * -((D\<^sup>T \<sqinter> -1) * -Dbot)"
    by (simp add: Datoms_def minimal_def mult_right_isotone)
  also have "... \<le> Dbot"
    by (metis complement_conv_sub conv_complement conv_dist_inf equivalence_one_closed schroeder_5)
  also have "... \<le> -Datoms"
    by (simp add: Datoms_def minimal_def)
  finally have "Datoms * Datoms\<^sup>T \<le> -D \<squnion> 1"
    by (simp add: schroeder_4_p)
  thus "D \<sqinter> Datoms \<sqinter> Datoms\<^sup>T \<le> 1"
    by (simp add: div_atoms_vector heyting.implies_galois_var inf_assoc vector_covector)
qed

lemma div_atomic_bot:
  assumes "D2_antisymmetric _"
      and "D6_least_surjective _"
    shows "D\<^sup>T * Datomsbot = top"
  using assms all_div_bot Datomsbot_def semiring.distrib_left by auto

lemma div_via_atom:
  assumes "D3_transitive _"
      and "D11_atomic _"
    shows "-Dbot \<sqinter> D \<le> D\<^sup>T * (D \<sqinter> Datoms)"
proof -
  have "D\<^sup>T * Datoms \<sqinter> D \<le> D\<^sup>T * (D \<sqinter> Datoms)"
    by (smt (verit, ccfv_SIG) assms(1) conv_involutive dedekind_1 inf.sup_monoid.add_commute inf.boundedI inf.order_lesseq_imp inf_le1 mult_right_isotone)
  thus ?thesis
    by (simp add: assms(2))
qed

lemma div_via_atom_bot:
  assumes "D1_reflexive _"
      and "D2_antisymmetric _"
      and "D3_transitive _"
      and "D6_least_surjective _"
    shows "D \<le> D\<^sup>T * (D \<sqinter> Datomsbot)"
proof -
  have "D\<^sup>T * Datomsbot \<sqinter> D \<le> D\<^sup>T * (D \<sqinter> Datomsbot)"
    by (metis assms(1,3) div_idempotent conv_involutive dedekind_1 inf.sup_monoid.add_commute)
  thus ?thesis
    by (simp add: assms(2,4) div_atomic_bot)
qed

lemma div_converse_via_atom:
  assumes "D3_transitive _"
      and "D11_atomic _"
    shows "-Dbot\<^sup>T \<sqinter> D\<^sup>T \<le> D\<^sup>T * (D \<sqinter> Datoms)"
proof -
  have "symmetric (D\<^sup>T * (D \<sqinter> Datoms))"
    by (simp add: div_atoms_vector conv_dist_comp conv_dist_inf covector_inf_comp_3 inf.sup_monoid.add_commute)
  thus ?thesis
    by (metis assms div_via_atom conv_complement conv_dist_inf conv_isotone)
qed

lemma div_converse_via_atom_bot:
  assumes "D1_reflexive _"
      and "D2_antisymmetric _"
      and "D3_transitive _"
      and "D6_least_surjective _"
    shows "D\<^sup>T \<le> D\<^sup>T * (D \<sqinter> Datomsbot)"
  by (metis assms div_atoms_bot_vector div_idempotent div_via_atom_bot comp_inf_vector conv_dist_comp conv_dist_inf conv_involutive schroeder_4 schroeder_6 symmetric_top_closed)

lemma div_comparable_via_atom:
  assumes "D3_transitive _"
      and "D11_atomic _"
    shows "-Dbot \<sqinter> -Dbot\<^sup>T \<sqinter> (D \<squnion> D\<^sup>T) \<le> D\<^sup>T * (D \<sqinter> Datoms)"
proof -
  have "-Dbot \<sqinter> -Dbot\<^sup>T \<sqinter> (D \<squnion> D\<^sup>T) = (-Dbot \<sqinter> -Dbot\<^sup>T \<sqinter> D) \<squnion> (-Dbot \<sqinter> -Dbot\<^sup>T \<sqinter> D\<^sup>T)"
    by (simp add: comp_inf.semiring.distrib_left)
  also have "... \<le> (-Dbot \<sqinter> D) \<squnion> (-Dbot\<^sup>T \<sqinter> D\<^sup>T)"
    by (metis comp_inf.coreflexive_comp_inf_comp comp_inf.semiring.add_mono inf.cobounded1 inf.cobounded2 top.extremum)
  also have "... \<le> D\<^sup>T * (D \<sqinter> Datoms)"
    by (simp add: assms div_converse_via_atom div_via_atom)
  finally show ?thesis
    .
qed

lemma div_comparable_via_atom_bot:
  assumes "D1_reflexive _"
      and "D2_antisymmetric _"
      and "D3_transitive _"
      and "D6_least_surjective _"
    shows "D \<squnion> D\<^sup>T \<le> D\<^sup>T * (D \<sqinter> Datomsbot)"
  by (simp add: assms div_converse_via_atom_bot div_via_atom_bot)

lemma div_atomic_iff_1:
  assumes "D3_transitive _"
    shows "D11_atomic _ \<longleftrightarrow> -Dbot \<le> D\<^sup>T * Datoms"
  using Datoms_def Dbot_def assms transitive_minimal_not_least by force

lemma div_atomic_iff_2:
  assumes "D3_transitive _"
    shows "D11_atomic _ \<longleftrightarrow> -D \<le> D\<^sup>T * Datoms"
  by (metis Dbot_def assms div_atomic_iff_1 div_atoms_vector div_least_div brouwer.p_antitone comp_associative double_compl inf_top.left_neutral least_def mult_left_isotone)

lemma div_atoms_antichain_minimal:
  assumes "D2_antisymmetric _"
      and "D3_transitive _"
      and "antichain D x"
      and "D\<^sup>T * x = -Dbot"
    shows "x = minimal D (-Dbot)"
proof (rule order.antisym)
  have 1: "x \<le> -Dbot"
    by (smt (verit, del_insts) assms(4) Dbot_def ex231d div_least_vector compl_le_compl_iff conv_complement_sub_leq conv_involutive double_compl inf_top.left_neutral least_def order_lesseq_imp schroeder_4_p top_right_mult_increasing)
  have "-Dbot \<le> ((D\<^sup>T \<sqinter> -1) \<squnion> 1) * x"
    by (metis assms(4) heyting.implies_galois_increasing mult_left_isotone regular_one_closed sup_commute)
  also have "... \<le> x \<squnion> (D\<^sup>T \<sqinter> -1) * x"
    by (simp add: mult_right_dist_sup)
  also have "... \<le> x \<squnion> (D\<^sup>T \<sqinter> -1) * -Dbot"
    using 1 mult_isotone sup_right_isotone by blast
  finally have "-Dbot \<sqinter> -((D\<^sup>T \<sqinter> -1) * -Dbot) \<le> x"
    using half_shunting sup_neg_inf by blast
  thus "minimal D (-Dbot) \<le> x"
    by (simp add: minimal_def)
  have 2: "D \<sqinter> -1 \<sqinter> x \<le> -x\<^sup>T"
    using assms(3) antichain_def inf.sup_monoid.add_commute inf_left_commute shunting_1 by auto
  have "D * (D \<sqinter> -1) \<le> D \<sqinter> -1"
    by (smt (verit, ccfv_threshold) assms(1,2) antisymmetric_inf_diversity conv_complement conv_involutive conv_order le_inf_iff mult_left_one mult_right_isotone order_lesseq_imp schroeder_4_p)
  hence "(D\<^sup>T \<sqinter> -1) * D\<^sup>T \<le> D\<^sup>T \<sqinter> -1"
    by (metis (mono_tags, opaque_lifting) conv_complement conv_dist_comp conv_dist_inf conv_order equivalence_one_closed)
  hence "(D\<^sup>T \<sqinter> -1) * -Dbot \<le> (D\<^sup>T \<sqinter> -1) * x"
    by (metis assms(4) comp_associative mult_left_isotone)
  also have "... = (D \<sqinter> -1 \<sqinter> x)\<^sup>T * top"
    using assms(3) antichain_def conv_complement conv_dist_inf covector_inf_comp_3 by auto
  also have "... \<le> -x * top"
    using 2 by (metis conv_complement conv_involutive conv_order mult_left_isotone)
  also have "... = -x"
    using assms(3) antichain_def complement_vector by auto
  finally show "x \<le> minimal D (-Dbot)"
    using 1 by (simp add: minimal_def p_antitone_iff)
qed

lemma div_atomic_iff_3:
  assumes "D2_antisymmetric _"
      and "D3_transitive _"
    shows "D11_atomic _ \<longleftrightarrow> (\<exists>x . antichain D x \<and> D\<^sup>T * x = -Dbot)"
  using Datoms_def assms div_atoms_antichain_minimal div_atoms_antichain by fastforce

text \<open>
The literal translation of axiom A12 is \<open>-Dbot \<le> -D\<^sup>T * Datoms\<close>.
However, this allows a model without atoms, where \<open>Dbot = top\<close> and \<open>Datoms = Dmono = Dfactor = bot\<close>.
Nitpick finds a counterexample to \<open>surjective Datoms\<close>.
With A2 and A12 the latter is equivalent to \<open>-D\<^sup>T * Datoms = top\<close>, which we use as a replacement for axiom A12.
\<close>

lemma div_atom_surjective:
  assumes "D12_infinite_base _"
    shows "surjective Datoms"
  by (metis assms invertible_surjective top_greatest)

lemma div_infinite_base_upperbound:
  assumes "D12_infinite_base _"
    shows "upperbound D Datoms = bot"
  by (simp add: assms upperbound_def)

lemma div_atom_surjective_iff_infinite_base:
  assumes "D2_antisymmetric _"
      and "-Dbot \<le> -D\<^sup>T * Datoms"
    shows "surjective Datoms \<longleftrightarrow> D12_infinite_base _"
proof (rule iffI)
  assume 1: "surjective Datoms"
  have 2: "Dbot \<sqinter> -Dbot\<^sup>T \<le> -D\<^sup>T"
    by (metis assms(1) div_least_converse conv_dist_inf conv_involutive conv_order double_compl inf.sup_monoid.add_commute p_shunting_swap)
  have "top = top * Datoms"
    using 1 by simp
  also have "... = top * (-Dbot \<sqinter> Datoms)"
    by (simp add: Datoms_def minimal_def)
  also have "... = -Dbot\<^sup>T * Datoms"
    by (metis complement_vector conv_complement covector_inf_comp_3 div_least_vector inf_top.left_neutral)
  finally have "Dbot = Dbot \<sqinter> -Dbot\<^sup>T * Datoms"
    by simp
  also have "... = (Dbot \<sqinter> -Dbot\<^sup>T) * Datoms"
    by (simp add: div_least_vector vector_inf_comp)
  also have "... \<le> -D\<^sup>T * Datoms"
    using 2 mult_left_isotone by auto
  finally have "Dbot \<le> -D\<^sup>T * Datoms"
    .
  thus "-D\<^sup>T * Datoms = top"
    by (metis assms(2) sup_absorb2 sup_shunt)
next
  assume "-D\<^sup>T * Datoms = top"
  thus "surjective Datoms"
    using div_atom_surjective by auto
qed

subsection \<open>Fibers\<close>

lemma div_mono_vector:
  "vector Dmono"
  by (simp add: Dmono_def comp_associative)

lemma div_mono_bot_vector:
  "vector Dmonobot"
  by (simp add: div_mono_vector Dmonobot_def div_least_vector vector_sup_closed)

lemma div_atom_mono_atom:
  "Datoms \<sqinter> D * (D\<^sup>T \<sqinter> Dmono) \<sqinter> Datoms\<^sup>T \<le> 1"
proof -
  let ?u = "univalent_part ((D \<sqinter> Datoms)\<^sup>T)"
  have 1: "D\<^sup>T \<sqinter> ?u * top \<le> ?u * (?u\<^sup>T * D\<^sup>T)"
    by (metis dedekind_1 inf.absorb_iff1 inf_commute top_greatest)
  have 2: "(Datoms \<sqinter> D) * ?u \<le> 1"
    by (metis conv_involutive inf.sup_monoid.add_commute univalent_part_times_converse_1)
  have "Datoms \<sqinter> D * (D\<^sup>T \<sqinter> Dmono) \<sqinter> Datoms\<^sup>T = (Datoms \<sqinter> D) * (D\<^sup>T \<sqinter> ?u * top) \<sqinter> Datoms\<^sup>T"
    by (metis div_atoms_vector Dmono_def vector_export_comp)
  also have "... \<le> (Datoms \<sqinter> D) * ?u * ?u\<^sup>T * D\<^sup>T \<sqinter> Datoms\<^sup>T"
    using 1 by (simp add: comp_associative inf.sup_monoid.add_commute le_infI2 mult_right_isotone)
  also have "... \<le> ?u\<^sup>T * D\<^sup>T \<sqinter> Datoms\<^sup>T"
    using 2 by (metis comp_inf.mult_left_isotone mult_left_isotone comp_associative comp_left_one)
  also have "... = ?u\<^sup>T * (D \<sqinter> Datoms)\<^sup>T"
    using div_atoms_vector conv_dist_inf covector_comp_inf vector_conv_covector by force
  also have "... = ?u\<^sup>T * ?u"
    by (metis conv_dist_comp conv_involutive univalent_part_times_converse)
  also have "... \<le> 1"
    by (simp add: univalent_part_univalent)
  finally show ?thesis
    .
qed

lemma div_atoms_mono:
  assumes "D1_reflexive _"
    shows "Datoms \<le> Dmono"
proof -
  have "D\<^sup>T \<sqinter> Datoms \<sqinter> Datoms\<^sup>T \<le> 1"
    by (smt (verit, ccfv_threshold) div_atoms_antichain antichain_def conv_dist_inf conv_involutive coreflexive_symmetric inf.left_commute inf.sup_monoid.add_commute)
  hence "1 \<sqinter> (D\<^sup>T \<sqinter> Datoms \<sqinter> Datoms\<^sup>T) * -1 \<le> bot"
    by (metis bot_least coreflexive_comp_top_inf inf_compl_bot_right)
  hence "1 \<sqinter> Datoms \<sqinter> (D\<^sup>T \<sqinter> Datoms\<^sup>T) * -1 \<le> bot"
    by (smt (verit, ccfv_threshold) div_atoms_vector inf.sup_monoid.add_commute inf_assoc vector_inf_comp)
  hence "1 \<sqinter> Datoms \<le> -((D\<^sup>T \<sqinter> Datoms\<^sup>T) * -1)"
    using le_bot pseudo_complement by blast
  hence "1 \<sqinter> Datoms \<sqinter> Datoms\<^sup>T \<le> D\<^sup>T \<sqinter> -((D\<^sup>T \<sqinter> Datoms\<^sup>T) * -1) \<sqinter> Datoms\<^sup>T"
    using comp_inf.mult_left_isotone assms reflexive_conv_closed by fastforce
  hence "(1 \<sqinter> Datoms \<sqinter> Datoms\<^sup>T) * top \<le> (D\<^sup>T \<sqinter> -((D\<^sup>T \<sqinter> Datoms\<^sup>T) * -1) \<sqinter> Datoms\<^sup>T) * top"
    using mult_left_isotone by blast
  hence "Datoms \<le> (D\<^sup>T \<sqinter> -((D\<^sup>T \<sqinter> Datoms\<^sup>T) * -1) \<sqinter> Datoms\<^sup>T) * top"
    by (smt (verit) div_atoms_vector inf.absorb2 inf.cobounded2 inf.left_commute inf_top.right_neutral one_inf_conv vector_export_comp_unit)
  also have "... = ((D \<sqinter> Datoms)\<^sup>T \<sqinter> -((D \<sqinter> Datoms)\<^sup>T * -1)) * top"
    by (smt (verit) conv_dist_inf inf.sup_monoid.add_assoc inf.sup_monoid.add_commute univalent_part_def)
  finally show ?thesis
    by (simp add: Dmono_def univalent_part_def)
qed

lemma div_mono_downclosed:
  assumes "D3_transitive _"
      and "D11_atomic _"
    shows "-Dbot \<sqinter> D * Dmono \<le> Dmono"
proof -
  let ?u = "univalent_part ((D \<sqinter> Datoms)\<^sup>T)"
  have "-Dbot \<sqinter> D * ?u = (-Dbot \<sqinter> D) * ?u"
    by (simp add: Dbot_def least_def vector_export_comp)
  also have "... \<le> D\<^sup>T * (D \<sqinter> Datoms) * ?u"
    by (simp add: assms div_via_atom mult_left_isotone)
  also have "... \<le> D\<^sup>T"
    by (metis comp_associative comp_right_one conv_involutive mult_right_isotone univalent_part_times_converse_1)
  finally have 1: "-Dbot \<sqinter> D * ?u \<le> D\<^sup>T"
    .
  have "(Datoms \<sqinter> D) * D \<le> Datoms \<sqinter> D"
    using assms(1) div_atoms_vector inf_mono vector_inf_comp by auto
  hence "D\<^sup>T * (D \<sqinter> Datoms)\<^sup>T * -1 \<le> (D \<sqinter> Datoms)\<^sup>T * -1"
    by (metis conv_dist_comp conv_isotone inf_commute mult_left_isotone)
  hence 2: "D * -((D \<sqinter> Datoms)\<^sup>T * -1) \<le> -((D \<sqinter> Datoms)\<^sup>T * -1)"
    by (simp add: comp_associative schroeder_3_p)
  have "D * ?u \<le> D * (D\<^sup>T \<sqinter> Datoms\<^sup>T) \<sqinter> D * -((D \<sqinter> Datoms)\<^sup>T * -1)"
    using comp_right_subdist_inf conv_dist_inf univalent_part_def by auto
  also have "... \<le> Datoms\<^sup>T \<sqinter> D * -((D \<sqinter> Datoms)\<^sup>T * -1)"
    using div_atoms_vector comp_inf.mult_left_isotone covector_comp_inf vector_conv_covector by force
  finally have "-Dbot \<sqinter> D * ?u \<le> D\<^sup>T \<sqinter> D * -((D \<sqinter> Datoms)\<^sup>T * -1) \<sqinter> Datoms\<^sup>T"
    using 1 by (simp add: inf.coboundedI2)
  also have "... \<le> D\<^sup>T \<sqinter> -((D \<sqinter> Datoms)\<^sup>T * -1) \<sqinter> Datoms\<^sup>T"
    using 2 comp_inf.comp_isotone by blast
  also have "... = ?u"
    by (smt (verit, ccfv_threshold) conv_dist_inf inf.sup_monoid.add_assoc inf.sup_monoid.add_commute univalent_part_def)
  finally have "-Dbot \<sqinter> D * ?u * top \<le> ?u * top"
    by (metis div_least_vector mult_left_isotone vector_complement_closed vector_inf_comp)
  thus "-Dbot \<sqinter> D * Dmono \<le> Dmono"
    by (simp add: Dmono_def comp_associative)
qed

lemma div_mono_bot_downclosed:
  assumes "D1_reflexive _"
      and "D3_transitive _"
      and "D11_atomic _"
    shows "D * Dmonobot \<le> Dmonobot"
proof -
  have "D * Dmonobot = D * Dmono \<squnion> D * Dbot"
    using Dmonobot_def comp_left_dist_sup by auto
  also have "... = (-Dbot \<sqinter> D * Dmono) \<squnion> Dbot"
    by (simp add: assms(1,2) bot_div_bot sup_commute)
  also have "... \<le> Dmonobot"
    using assms div_mono_downclosed Dmonobot_def sup_left_isotone by auto
  finally show ?thesis
    .
qed

lemma div_least_not_mono:
  assumes "D2_antisymmetric _"
    shows "Dbot \<le> -Dmono"
proof -
  let ?u = "univalent_part ((D \<sqinter> Datoms)\<^sup>T)"
  have 1: "Dbot \<sqinter> D\<^sup>T \<le> Dbot\<^sup>T"
    by (metis assms div_least_converse conv_dist_inf conv_involutive conv_order inf.sup_monoid.add_commute)
  have "Dbot \<sqinter> ?u \<le> Dbot \<sqinter> D\<^sup>T \<sqinter> Datoms\<^sup>T"
    using conv_dist_inf inf.sup_left_divisibility inf_assoc univalent_part_def by auto
  also have "... \<le> Dbot\<^sup>T \<sqinter> Datoms\<^sup>T"
    using 1 inf.sup_left_isotone by blast
  also have "... \<le> bot"
    by (metis div_least_not_atom bot_least conv_dist_inf coreflexive_symmetric pseudo_complement)
  finally show ?thesis
    by (metis Dmono_def compl_le_swap1 div_least_vector inf_top.right_neutral mult_left_isotone p_top pseudo_complement vector_complement_closed)
qed

lemma div_fibered_transitive_1:
  assumes "D1_reflexive _"
      and "D2_antisymmetric _"
      and "D3_transitive _"
      and "D11_atomic _"
    shows "Dmono \<sqinter> D\<^sup>T * (Datoms \<sqinter> D) \<sqinter> Dmono\<^sup>T = Dmono \<sqinter> (D \<squnion> D\<^sup>T) * (Dmono \<sqinter> (D \<squnion> D\<^sup>T)) \<sqinter> Dmono\<^sup>T"
proof (rule order.antisym)
  show "Dmono \<sqinter> D\<^sup>T * (Datoms \<sqinter> D) \<sqinter> Dmono\<^sup>T \<le> Dmono \<sqinter> (D \<squnion> D\<^sup>T) * (Dmono \<sqinter> (D \<squnion> D\<^sup>T)) \<sqinter> Dmono\<^sup>T"
    using assms(1) div_atoms_mono comp_inf.mult_right_isotone inf.sup_left_isotone inf.sup_mono mult_isotone sup.cobounded1 sup_ge2 by auto
  have "Dmono \<sqinter> (D \<squnion> D\<^sup>T) * (Dmono \<sqinter> (D \<squnion> D\<^sup>T)) \<sqinter> Dmono\<^sup>T = (Dmono \<sqinter> (D \<squnion> D\<^sup>T) \<sqinter> Dmono\<^sup>T) * (Dmono \<sqinter> (D \<squnion> D\<^sup>T)) \<sqinter> Dmono\<^sup>T"
    by (metis div_mono_vector covector_inf_comp_2 vector_export_comp)
  also have "... \<le> (-Dbot \<sqinter> (D \<squnion> D\<^sup>T) \<sqinter> Dmono\<^sup>T) * (Dmono \<sqinter> (D \<squnion> D\<^sup>T)) \<sqinter> Dmono\<^sup>T"
    using assms(2) div_least_not_mono comp_inf.mult_left_isotone compl_le_swap1 mult_left_isotone by auto
  also have "... \<le> (-Dbot \<sqinter> (D \<squnion> D\<^sup>T) \<sqinter> -Dbot\<^sup>T) * (Dmono \<sqinter> (D \<squnion> D\<^sup>T)) \<sqinter> Dmono\<^sup>T"
    by (smt (verit) assms(2) div_least_not_mono compl_le_compl_iff conv_complement conv_order double_compl inf.sup_monoid.add_commute inf.sup_right_isotone mult_left_isotone)
  also have "... \<le> D\<^sup>T * (D \<sqinter> Datoms) * (Dmono \<sqinter> (D \<squnion> D\<^sup>T)) \<sqinter> Dmono\<^sup>T"
    by (smt (verit, del_insts) assms(3,4) div_comparable_via_atom inf_commute inf_left_commute inf_sup_distrib1 mult_right_dist_sup sup.order_iff)
  also have "... = D\<^sup>T * (D \<sqinter> Datoms \<sqinter> Dmono\<^sup>T) * (Dmono \<sqinter> (D \<squnion> D\<^sup>T) \<sqinter> Dmono\<^sup>T)"
    by (smt (verit, ccfv_SIG) div_mono_vector covector_comp_inf covector_inf_comp_2 vector_conv_covector)
  also have "... \<le> D\<^sup>T * (D \<sqinter> Datoms \<sqinter> Dmono\<^sup>T) * (-Dbot \<sqinter> (D \<squnion> D\<^sup>T) \<sqinter> Dmono\<^sup>T)"
    using assms(2) div_least_not_mono comp_inf.mult_left_isotone compl_le_swap1 mult_right_isotone by auto
  also have "... \<le> D\<^sup>T * (D \<sqinter> Datoms \<sqinter> Dmono\<^sup>T) * (-Dbot \<sqinter> (D \<squnion> D\<^sup>T) \<sqinter> -Dbot\<^sup>T)"
    by (metis assms(2) div_least_not_mono comp_inf.mult_right_isotone compl_le_swap1 conv_complement conv_order mult_right_isotone)
  also have "... = D\<^sup>T * (D \<sqinter> Datoms \<sqinter> Dmono\<^sup>T) * (-Dbot \<sqinter> (D \<squnion> D\<^sup>T) \<sqinter> -Dbot\<^sup>T)\<^sup>T"
    using conv_complement conv_dist_inf conv_dist_sup conv_involutive inf.sup_monoid.add_commute inf_assoc sup_commute by auto
  also have "... \<le> D\<^sup>T * (D \<sqinter> Datoms \<sqinter> Dmono\<^sup>T) * (D\<^sup>T * (D \<sqinter> Datoms))\<^sup>T"
    using assms(3,4) div_comparable_via_atom conv_order inf.sup_monoid.add_commute inf_assoc mult_right_isotone by auto
  also have "... = D\<^sup>T * (D \<sqinter> Datoms \<sqinter> Dmono\<^sup>T) * (D \<sqinter> Datoms)\<^sup>T * D"
    by (simp add: comp_associative conv_dist_comp)
  also have "... = D\<^sup>T * (Datoms \<sqinter> D * (Dmono \<sqinter> D\<^sup>T) \<sqinter> Datoms\<^sup>T) * D"
    by (smt (verit, ccfv_threshold) div_atoms_vector div_mono_vector comp_associative conv_dist_inf covector_inf_comp_3 inf.sup_monoid.add_commute)
  also have "... = D\<^sup>T * (Datoms \<sqinter> D * (Dmono \<sqinter> D\<^sup>T) \<sqinter> Datoms\<^sup>T) * (Datoms \<sqinter> D)"
    using div_atoms_vector covector_comp_inf covector_inf_comp_3 vector_conv_covector by auto
  also have "... \<le> D\<^sup>T * (Datoms \<sqinter> D)"
    by (metis div_atom_mono_atom comp_right_one inf.sup_monoid.add_commute mult_left_isotone mult_right_isotone)
  finally show "Dmono \<sqinter> (D \<squnion> D\<^sup>T) * (Dmono \<sqinter> (D \<squnion> D\<^sup>T)) \<sqinter> Dmono\<^sup>T \<le> Dmono \<sqinter> D\<^sup>T * (Datoms \<sqinter> D) \<sqinter> Dmono\<^sup>T"
    by (simp add: inf.coboundedI2 inf.sup_monoid.add_commute)
qed

lemma div_fibered_iff:
  assumes "D1_reflexive _"
      and "D2_antisymmetric _"
      and "D3_transitive _"
      and "D11_atomic _"
    shows "D8_fibered _ \<longleftrightarrow> Dmono \<sqinter> (D \<squnion> D\<^sup>T) * (Dmono \<sqinter> (D \<squnion> D\<^sup>T)) \<sqinter> Dmono\<^sup>T \<le> D \<squnion> D\<^sup>T"
  using assms div_fibered_transitive_1 by auto

lemma div_fibered_transitive:
  assumes "D1_reflexive _"
      and "D2_antisymmetric _"
      and "D3_transitive _"
      and "D8_fibered _"
      and "D11_atomic _"
    shows "Dmono \<sqinter> (D \<squnion> D\<^sup>T) * (Dmono \<sqinter> (D \<squnion> D\<^sup>T)) \<sqinter> Dmono\<^sup>T \<le> D \<squnion> D\<^sup>T"
  using assms div_fibered_transitive_1 by auto

subsection \<open>Fiber decomposition\<close>

lemma div_factor_div_mono:
  "Dfactor \<le> D \<sqinter> Dmono"
  by (metis Dfactor_def inf.cobounded1 maximal_def)

lemma div_factor_div:
  "Dfactor \<le> D"
  using div_factor_div_mono by auto

lemma div_factor_mono:
  "Dfactor \<le> Dmono"
  using div_factor_div_mono by auto

lemma div_factor_one_mono:
  "Dfactor \<sqinter> 1 \<le> Dmono"
  using div_factor_mono inf.coboundedI1 by blast

lemma div_pre_f_decomposable_1:
  assumes "D2_antisymmetric _"
      and "D7_pre_f_decomposable _"
    shows "upperbound D (D \<sqinter> Dmono) \<le> D\<^sup>T"
  using assms supremum_upperbound by force

lemma div_pre_f_decomposable_iff:
  assumes "D2_antisymmetric _"
    shows "D7_pre_f_decomposable _ \<longleftrightarrow> upperbound D (D \<sqinter> Dmono) \<le> D\<^sup>T"
  using assms supremum_upperbound by force

lemma div_pre_f_decomposable_char:
  assumes "D2_antisymmetric _"
      and "D7_pre_f_decomposable _"
    shows "upperbound D (D \<sqinter> Dmono) \<sqinter> (upperbound D (D \<sqinter> Dmono))\<^sup>T = 1"
proof (rule order.antisym)
  have "1 \<le> upperbound D (D \<sqinter> Dmono)"
    by (simp add: compl_le_swap1 conv_complement schroeder_3_p upperbound_def)
  thus "1 \<le> upperbound D (D \<sqinter> Dmono) \<sqinter> (upperbound D (D \<sqinter> Dmono))\<^sup>T"
    using le_inf_iff reflexive_conv_closed by blast
  have "upperbound D (D \<sqinter> Dmono) \<sqinter> (upperbound D (D \<sqinter> Dmono))\<^sup>T \<le> D\<^sup>T \<sqinter> D"
    by (metis assms comp_inf.comp_isotone conv_involutive conv_order div_pre_f_decomposable_1)
  thus "upperbound D (D \<sqinter> Dmono) \<sqinter> (upperbound D (D \<sqinter> Dmono))\<^sup>T \<le> 1"
    by (metis assms(1) inf.absorb2 inf.boundedE inf_commute)
qed

lemma div_factor_bot:
  assumes "D1_reflexive _"
      and "D2_antisymmetric _"
      and "D3_transitive _"
      and "D11_atomic _"
    shows "Dfactorbot = Dfactor \<squnion> (Dbot \<sqinter> Dbot\<^sup>T)"
proof -
  have "Dbot \<sqinter> Datoms\<^sup>T \<le> -1"
    by (metis comp_inf.semiring.mult_not_zero div_least_not_atom inf.sup_monoid.add_commute inf_left_commute one_inf_conv pseudo_complement)
  hence "Dbot \<sqinter> Datoms\<^sup>T * D = (Dbot \<sqinter> Datoms\<^sup>T \<sqinter> -1) * D"
    by (simp add: div_least_vector inf.absorb1 vector_inf_comp)
  also have "... = (Dbot \<sqinter> -1) * (D \<sqinter> Datoms)"
    by (smt (verit, del_insts) div_atoms_vector comp_inf_vector conv_dist_comp inf.sup_monoid.add_assoc inf.sup_monoid.add_commute symmetric_top_closed)
  also have "... \<le> (D \<sqinter> -1) * (D \<sqinter> Dmono)"
    using assms(1) div_atoms_mono div_least_div comp_isotone inf.sup_mono order_refl by blast
  finally have 1: "Dbot \<sqinter> Datoms\<^sup>T * D \<le> (D \<sqinter> -1) * (D \<sqinter> Dmono)"
    .
  hence 1: "Dbot \<sqinter> -((D \<sqinter> -1) * (D \<sqinter> Dmono)) \<le> Dbot\<^sup>T"
    by (metis assms(4) conv_complement conv_dist_comp conv_involutive double_compl p_shunting_swap)
  have "Dbot \<sqinter> Dbot\<^sup>T \<sqinter> (D \<sqinter> -1) * (D \<sqinter> Dmono) \<le> Dbot\<^sup>T \<sqinter> (D \<sqinter> -1) * D"
    using comp_inf.mult_right_isotone comp_right_subdist_inf inf.sup_monoid.add_assoc by force
  also have "... = bot"
    by (smt (verit, best) assms bot_div_bot div_atoms_vector div_strict_bot comp_associative comp_inf.vector_bot_closed complement_vector conv_dist_comp schroeder_2 symmetric_top_closed)
  finally have "Dbot \<sqinter> Dbot\<^sup>T \<le> -((D \<sqinter> -1) * (D \<sqinter> Dmono))"
    using le_bot pseudo_complement by blast
  hence 2: "Dbot \<sqinter> -((D \<sqinter> -1) * (D \<sqinter> Dmono)) = Dbot \<sqinter> Dbot\<^sup>T"
    using 1 by (smt (verit, del_insts) inf.absorb1 inf.sup_monoid.add_assoc inf_commute)
  have "Dfactorbot = D \<sqinter> (Dmono \<squnion> Dbot) \<sqinter> -((D \<sqinter> -1) * (D \<sqinter> Dmono)) \<sqinter> -((D \<sqinter> -1) * (D \<sqinter> Dbot))"
    by (simp add: Dfactorbot_def Dmonobot_def comp_inf.vector_inf_comp inf_sup_distrib1 maximal_def mult_left_dist_sup)
  also have "... = D \<sqinter> (Dmono \<squnion> Dbot) \<sqinter> -((D \<sqinter> -1) * (D \<sqinter> Dmono))"
    by (simp add: assms(2) div_strict_bot div_least_div inf.absorb2)
  also have "... = Dfactor \<squnion> (Dbot \<sqinter> -((D \<sqinter> -1) * (D \<sqinter> Dmono)))"
    using div_least_div Dfactor_def comp_inf.mult_right_dist_sup inf.absorb2 inf_sup_distrib1 maximal_def by auto
  finally show ?thesis
    using 2 by auto
qed

lemma div_factor_surjective:
  assumes "D1_reflexive _"
      and "D3_transitive _"
      and "D9_f_decomposable _"
      and "D11_atomic _"
    shows "surjective (Dbot\<^sup>T \<squnion> Dfactor)"
proof -
  have "D \<sqinter> Datoms \<le> top * Dfactor"
    by (metis assms(3) inf.sup_monoid.add_commute mult_left_isotone order_lesseq_imp top_greatest)
  hence "D\<^sup>T * (D \<sqinter> Datoms) \<le> top * Dfactor"
    by (metis covector_mult_closed mult_isotone top_greatest vector_top_closed)
  hence "-Dbot \<sqinter> D \<le> top * Dfactor"
    using assms(2,4) div_via_atom by auto
  hence "top * (-Dbot \<sqinter> D) \<le> top * Dfactor"
    by (metis comp_associative mult_right_isotone vector_top_closed)
  hence "-Dbot\<^sup>T * D \<le> top * Dfactor"
    by (simp add: Dbot_def comp_inf_vector conv_complement conv_dist_comp inf.sup_monoid.add_commute least_def)
  hence "-Dbot\<^sup>T \<le> top * Dfactor"
    by (metis assms(1) bot_least case_split_right inf.sup_monoid.add_commute maddux_3_21 semiring.mult_not_zero shunting_1 sup.cobounded2)
  hence "top \<le> Dbot\<^sup>T \<squnion> top * Dfactor"
    by (simp add: sup_neg_inf)
  thus ?thesis
    using div_least_vector mult_left_dist_sup top_le vector_conv_covector by auto
qed

lemma div_factor_bot_surjective:
  assumes "D1_reflexive _"
      and "D2_antisymmetric _"
      and "D3_transitive _"
      and "D9_f_decomposable _"
      and "D11_atomic _"
    shows "surjective Dfactorbot"
proof -
  have "top * (Dbot \<sqinter> Dbot\<^sup>T) = top * Dbot\<^sup>T"
    by (smt (verit) conv_dist_comp covector_inf_comp_3 div_least_vector ex231d mult_right_isotone order.eq_iff top_greatest vector_conv_covector vector_covector vector_top_closed)
  thus ?thesis
    using assms div_factor_bot div_factor_surjective mult_left_dist_sup sup_monoid.add_commute by force
qed

lemma div_factor_surjective_2:
  assumes "D1_reflexive _"
      and "D3_transitive _"
      and "D9_f_decomposable _"
      and "D11_atomic _"
    shows "-D \<le> Dfactor\<^sup>T * top"
proof -
  have "-D\<^sup>T \<le> -Dbot\<^sup>T"
    using div_least_div conv_order by auto
  also have "... \<le> top * Dfactor"
    by (metis assms div_factor_surjective conv_dist_comp equivalence_top_closed mult_left_dist_sup sup_shunt div_least_vector)
  finally show ?thesis
    by (metis conv_complement conv_dist_comp conv_involutive conv_order equivalence_top_closed)
qed

lemma div_conv_factor_div_factor:
  assumes "D1_reflexive _"
    shows "Dmono \<sqinter> D\<^sup>T * Dfactor \<sqinter> D \<le> D * Dfactor"
proof -
  have "-(1 \<squnion> -D\<^sup>T)\<^sup>T * (Dmono \<sqinter> D) \<le> (D \<sqinter> -1) * (D \<sqinter> Dmono)"
    by (simp add: conv_complement conv_dist_sup inf.sup_monoid.add_commute)
  hence "(Dmono \<sqinter> D) * -((D \<sqinter> -1) * (D \<sqinter> Dmono))\<^sup>T \<le> 1 \<squnion> -D\<^sup>T"
    using schroeder_5 schroeder_6 by blast
  hence 1: "Dmono \<sqinter> D\<^sup>T \<sqinter> D * -((D \<sqinter> -1) * (D \<sqinter> Dmono))\<^sup>T \<le> 1"
    by (simp add: Dmono_def heyting.implies_galois_var inf.sup_monoid.add_commute inf_assoc inf_vector_comp sup_commute)
  have "Dfactor\<^sup>T \<le> -((D \<sqinter> -1) * (D \<sqinter> Dmono))\<^sup>T"
    by (metis Dfactor_def conv_complement conv_order inf.sup_right_divisibility maximal_def)
  hence 2: "Dmono \<sqinter> D\<^sup>T \<sqinter> D * Dfactor\<^sup>T \<le> 1"
    using 1 by (meson inf.sup_right_isotone mult_right_isotone order_trans)
  hence "(Dmono \<sqinter> D\<^sup>T \<sqinter> D * Dfactor\<^sup>T) * Dfactor \<sqinter> D \<le> D * Dfactor"
    using assms(1) dual_order.trans inf.coboundedI1 mult_left_isotone by blast
  thus ?thesis
    using 2 by (smt (verit, del_insts) div_factor_div Dmono_def coreflexive_comp_top_inf dedekind_2 dual_order.trans inf.absorb1 inf_assoc vector_export_comp)
qed

lemma div_f_decomposable_mono:
  assumes "D1_reflexive _"
      and "D2_antisymmetric _"
      and "D3_transitive _"
      and "D8_fibered _"
      and "D9_f_decomposable _"
      and "D11_atomic _"
    shows "Dmono \<sqinter> D \<le> D * Dfactor"
proof -
  have "Dmono \<sqinter> D = Dmono \<sqinter> -Dbot \<sqinter> D"
    by (metis assms(2) div_least_not_mono compl_le_swap1 inf.order_iff)
  also have "... = Dmono \<sqinter> D\<^sup>T * (D \<sqinter> Datoms) \<sqinter> D"
    by (smt (verit, ccfv_SIG) assms(2,3,6) div_least_not_mono div_via_atom compl_le_swap1 inf.le_iff_sup inf_assoc inf_left_commute)
  also have "... = Dmono \<sqinter> D\<^sup>T * (D \<sqinter> Datoms \<sqinter> D * Dfactor) \<sqinter> D"
    using assms(5) inf.le_iff_sup inf.sup_monoid.add_commute by auto
  also have "... = Dmono \<sqinter> D\<^sup>T * (D \<sqinter> Datoms \<sqinter> D * (Dmono \<sqinter> Dfactor)) \<sqinter> D"
    using div_factor_mono inf.le_iff_sup by fastforce
  also have "... = Dmono \<sqinter> D\<^sup>T * (D \<sqinter> (Datoms \<sqinter> D \<sqinter> Dmono\<^sup>T) * Dfactor) \<sqinter> D"
    using div_atoms_vector div_mono_vector covector_inf_comp_3 inf.sup_monoid.add_assoc vector_inf_comp by auto
  also have "... \<le> Dmono \<sqinter> D\<^sup>T * (Datoms \<sqinter> D \<sqinter> Dmono\<^sup>T) * Dfactor \<sqinter> D"
    by (simp add: comp_associative inf.coboundedI2 inf.sup_monoid.add_commute mult_right_isotone)
  also have "... = Dmono \<sqinter> (Dmono \<sqinter> D\<^sup>T * (Datoms \<sqinter> D) \<sqinter> Dmono\<^sup>T) * Dfactor \<sqinter> D"
    by (metis div_mono_vector covector_comp_inf inf.left_idem vector_conv_covector vector_export_comp)
  also have "... \<le> Dmono \<sqinter> (D \<squnion> D\<^sup>T) * Dfactor \<sqinter> D"
    by (metis assms(4) inf.sup_monoid.add_commute inf.sup_right_isotone mult_left_isotone)
  also have "... = (Dmono \<sqinter> D * Dfactor \<sqinter> D) \<squnion> (Dmono \<sqinter> D\<^sup>T * Dfactor \<sqinter> D)"
    by (simp add: inf_sup_distrib1 inf_sup_distrib2 mult_right_dist_sup)
  also have "... \<le> D * Dfactor"
    by (simp add: assms(1) div_conv_factor_div_factor inf.coboundedI1)
  finally show ?thesis
    .
qed

lemma div_pre_f_decomposable_2:
  assumes "D2_antisymmetric _"
      and "D7_pre_f_decomposable _"
    shows "-D \<le> (D \<sqinter> Dmono)\<^sup>T * -D"
  by (metis assms brouwer.p_antitone_iff conv_complement conv_dist_comp conv_involutive conv_order div_pre_f_decomposable_1 upperbound_def)

lemma div_f_decomposable_char_1:
  assumes "D1_reflexive _"
      and "D2_antisymmetric _"
      and "D3_transitive _"
      and "D7_pre_f_decomposable _"
      and "D8_fibered _"
      and "D9_f_decomposable _"
      and "D11_atomic _"
    shows "Dfactor\<^sup>T * -D = -D"
proof (rule order.antisym)
  have "Dfactor * D \<le> D"
    using assms(3) div_factor_div dual_order.trans mult_left_isotone by blast
  thus "Dfactor\<^sup>T * -D \<le> -D"
    by (simp add: schroeder_3_p)
  have "-D \<le> (D \<sqinter> Dmono)\<^sup>T * -D"
    by (simp add: assms(2,4) div_pre_f_decomposable_2)
  also have "... \<le> Dfactor\<^sup>T * D\<^sup>T * -D"
    by (metis assms(1-3,5-7) div_f_decomposable_mono conv_dist_comp conv_order inf_commute mult_left_isotone)
  also have "... \<le> Dfactor\<^sup>T * -D"
    using assms(3) comp_associative mult_right_isotone schroeder_3 by auto
  finally show "-D \<le> Dfactor\<^sup>T * -D"
    .
qed

lemma div_f_decomposable_char_2:
  assumes "D1_reflexive _"
      and "D2_antisymmetric _"
      and "D3_transitive _"
      and "D7_pre_f_decomposable _"
      and "D8_fibered _"
      and "D9_f_decomposable _"
      and "D11_atomic _"
    shows "noyau Dfactor = 1"
proof (rule order.antisym)
  show "reflexive (noyau Dfactor)"
    by (simp add: noyau_reflexive)
  have "-(Dfactor\<^sup>T * -Dfactor) \<le> -(Dfactor\<^sup>T * -D)"
    by (simp add: div_factor_div mult_right_isotone)
  also have "... = D"
    by (simp add: assms div_f_decomposable_char_1)
  finally have 1: "-(Dfactor\<^sup>T * -Dfactor) \<le> D"
    .
  hence "-(-Dfactor\<^sup>T * Dfactor) \<le> D\<^sup>T"
    by (metis conv_complement conv_dist_comp conv_involutive conv_order)
  thus "noyau Dfactor \<le> 1"
    using 1 assms(1,2) div_antisymmetric_equal comp_inf.comp_isotone symmetric_quotient_def by force
qed

lemma div_mono_one_div_factor:
  assumes "D1_reflexive _"
      and "D2_antisymmetric _"
    shows "Dmono \<sqinter> 1 \<le> Dfactor"
proof -
  have "Dmono \<sqinter> 1 \<sqinter> (D \<sqinter> -1) * (D \<sqinter> Dmono) \<le> 1 \<sqinter> (D \<sqinter> -1) * D"
    by (meson comp_inf.mult_right_isotone comp_right_subdist_inf inf.bounded_iff)
  also have "... \<le> bot"
    by (metis assms(2) compl_le_swap1 dual_order.eq_iff inf_shunt mult_1_left p_shunting_swap schroeder_4_p double_compl)
  finally have 1: "Dmono \<sqinter> 1 \<le> -((D \<sqinter> -1) * (D \<sqinter> Dmono))"
    using le_bot pseudo_complement by auto
  have "Dmono \<sqinter> 1 \<le> D \<sqinter> Dmono"
    by (simp add: assms(1) le_infI2)
  thus ?thesis
    using 1 by (simp add: Dfactor_def maximal_def)
qed

lemma div_mono_one_div_factor_one:
  assumes "D1_reflexive _"
      and "D2_antisymmetric _"
    shows "Dmono \<sqinter> 1 = Dfactor \<sqinter> 1"
  using assms div_mono_one_div_factor div_factor_mono inf.sup_same_context le_infI1 by blast

lemma div_factor_div_mono_div_factor:
  assumes "D1_reflexive _"
      and "D2_antisymmetric _"
      and "D3_transitive _"
      and "D8_fibered _"
      and "D9_f_decomposable _"
      and "D11_atomic _"
    shows "Dfactor * D = Dmono \<sqinter> D * Dfactor"
proof (rule order.antisym)
  have "Dfactor * D \<le> D * Dfactor"
    by (smt (verit, best) assms div_f_decomposable_mono div_factor_div_mono div_idempotent div_mono_vector comp_isotone inf_commute order_trans vector_export_comp)
  thus "Dfactor * D \<le> Dmono \<sqinter> D * Dfactor"
    by (metis div_factor_mono div_mono_vector inf.boundedI mult_isotone top_greatest)
  have "Dmono \<sqinter> D * Dfactor \<le> Dmono \<sqinter> D * D"
    using div_factor_div comp_inf.mult_isotone mult_isotone by blast
  also have "... \<le> Dmono \<sqinter> D"
    by (simp add: assms(3) inf.coboundedI1 inf_commute)
  also have "... = (Dmono \<sqinter> 1) * D"
    by (simp add: div_mono_vector vector_inf_one_comp)
  also have "... \<le> Dfactor * D"
    by (simp add: assms(1,2) div_mono_one_div_factor mult_left_isotone)
  finally show "Dmono \<sqinter> D * Dfactor \<le> Dfactor * D"
    .
qed

lemma div_mono_strict_div_factor:
  assumes "D1_reflexive _"
      and "D2_antisymmetric _"
      and "D3_transitive _"
    shows "Dmono \<sqinter> (D \<sqinter> -1) * Dfactor \<le> Dfactor * (D \<sqinter> -1)"
proof -
  have "Dmono \<sqinter> (D \<sqinter> -1) * Dfactor \<le> Dmono \<sqinter> (D \<sqinter> -1) * D"
    using div_factor_div comp_inf.mult_isotone mult_isotone by blast
  also have "... \<le> Dmono \<sqinter> D \<sqinter> -1"
    using assms(2,3) comp_inf.semiring.mult_left_mono strict_order_transitive_2 by auto
  also have "... = (Dmono \<sqinter> 1) * (D \<sqinter> -1)"
    by (simp add: div_mono_vector inf.sup_monoid.add_assoc vector_inf_one_comp)
  also have "... \<le> Dfactor * (D \<sqinter> -1)"
    by (simp add: assms(1,2) div_mono_one_div_factor mult_left_isotone)
  finally show ?thesis
    .
qed

lemma div_factor_div_strict:
  assumes "D1_reflexive _"
      and "D2_antisymmetric _"
      and "D3_transitive _"
      and "D8_fibered _"
      and "D9_f_decomposable _"
      and "D11_atomic _"
    shows "Dfactor * D \<sqinter> -1 = Dfactor * (D \<sqinter> -1)"
proof (rule order.antisym)
  have "Dfactor * D \<sqinter> -1 \<le> Dmono \<sqinter> D \<sqinter> -1"
    by (metis assms div_factor_div div_factor_div_mono_div_factor div_idempotent inf.bounded_iff inf.cobounded1 inf.sup_left_isotone mult_left_isotone)
  also have "... = (Dmono \<sqinter> 1) * (D \<sqinter> -1)"
    by (simp add: div_mono_vector inf.sup_monoid.add_assoc vector_inf_one_comp)
  also have "... \<le> Dfactor * (D \<sqinter> -1)"
    using assms(1,2) div_mono_one_div_factor mult_left_isotone by auto
  finally show "Dfactor * D \<sqinter> -1 \<le> Dfactor * (D \<sqinter> -1)"
    .
  have "Dfactor * (D \<sqinter> -1) \<le> D * (D \<sqinter> -1)"
    by (simp add: div_factor_div mult_left_isotone)
  also have "... \<le> -1"
    by (simp add: assms(1,2,3) strict_order_transitive_eq_2)
  finally show "Dfactor * (D \<sqinter> -1) \<le> Dfactor * D \<sqinter> -1"
    by (simp add: mult_right_isotone)
qed

lemma div_factor_strict:
  assumes "D1_reflexive _"
      and "D2_antisymmetric _"
      and "D3_transitive _"
      and "D8_fibered _"
      and "D9_f_decomposable _"
      and "D11_atomic _"
    shows "Dfactor \<sqinter> -1 \<le> Dfactor * (D \<sqinter> -1)"
  by (metis assms div_factor_div_strict comp_right_one inf.sup_monoid.add_commute inf.sup_right_isotone mult_right_isotone)

lemma div_factor_div_mono_div:
  assumes "D1_reflexive _"
      and "D2_antisymmetric _"
      and "D3_transitive _"
    shows "Dfactor * D = Dmono \<sqinter> D"
proof (rule order.antisym)
  show "Dfactor * D \<le> Dmono \<sqinter> D"
    by (smt (verit, ccfv_SIG) assms(3) div_factor_div div_factor_mono div_mono_vector comp_isotone inf.boundedI inf.order_trans order.refl top_greatest)
  show "Dmono \<sqinter> D \<le> Dfactor * D"
    by (metis assms(1,2) div_mono_one_div_factor div_mono_vector mult_left_isotone vector_export_comp_unit)
qed

lemma div_factor_div_div_factor:
  assumes "D1_reflexive _"
      and "D2_antisymmetric _"
      and "D3_transitive _"
      and "D8_fibered _"
      and "D9_f_decomposable _"
      and "D11_atomic _"
    shows "Dfactor * D \<le> D * Dfactor"
  by (simp add: assms div_factor_div_mono_div_factor)

lemma div_f_decomposable_eq:
  assumes "D3_transitive _"
      and "D9_f_decomposable _"
    shows "Datoms \<sqinter> D = Datoms \<sqinter> D * Dfactor"
  by (smt (verit, ccfv_threshold) assms div_factor_div inf.absorb2 inf.sup_monoid.add_assoc inf_commute mult_isotone mult_right_isotone)

lemma div_f_decomposable_iff_1:
  assumes "D3_transitive _"
    shows "D9_f_decomposable _ \<longleftrightarrow> Datoms \<sqinter> D = Datoms \<sqinter> D * Dfactor"
  using assms div_f_decomposable_eq by fastforce

lemma div_f_decomposable_iff_2:
  assumes "D3_transitive _"
    shows "Dmono \<sqinter> D \<le> D * Dfactor \<longleftrightarrow> Dmono \<sqinter> D = Dmono \<sqinter> D * Dfactor"
  by (smt (verit, ccfv_SIG) assms div_factor_div div_mono_vector inf.absorb1 inf.cobounded2 inf.le_iff_sup inf.sup_monoid.add_assoc mult_isotone vector_inf_comp)

lemma div_factor_not_bot_conv:
  assumes "D2_antisymmetric _"
    shows "Dfactor \<le> -Dbot\<^sup>T"
  by (smt (verit, best) assms div_least_converse div_least_not_mono div_factor_div_mono inf.absorb2 inf.coboundedI1 p_shunting_swap)

lemma div_total_top_factor:
  assumes "D2_antisymmetric _"
      and "D6_least_surjective _"
    shows "total (-(top * Dfactor))"
proof -
  have "top = -(top * -Dbot\<^sup>T) * top"
    using assms div_least_point surjective_conv_total vector_conv_compl by auto
  also have "... \<le> -(top * Dfactor) * top"
    by (simp add: assms(1) div_factor_not_bot_conv mult_isotone)
  finally show ?thesis
    by (simp add: dual_order.antisym)
qed

lemma dif_f_decomposable_iff_3:
  assumes "D1_reflexive _"
      and "D2_antisymmetric _"
      and "D3_transitive _"
      and "D8_fibered _"
      and "D11_atomic _"
    shows "D9_f_decomposable _ \<longleftrightarrow> Dmono \<sqinter> D \<le> D * Dfactor"
  using assms div_atoms_mono div_f_decomposable_iff_1 div_f_decomposable_iff_2 div_f_decomposable_mono inf.sup_relative_same_increasing by blast

subsection \<open>Support\<close>

lemma div_support_div:
  assumes "D1_reflexive _"
      and "D2_antisymmetric _"
      and "D3_transitive _"
      and "D7_pre_f_decomposable _"
      and "D8_fibered _"
      and "D9_f_decomposable _"
      and "D11_atomic _"
    shows "Dsupport \<le> D\<^sup>T"
proof -
  have "-D\<^sup>T = -D\<^sup>T * Dfactor"
    by (metis assms div_f_decomposable_char_1 conv_complement conv_dist_comp conv_involutive)
  also have "... \<le> -(Datoms \<sqinter> D)\<^sup>T * Dfactor"
    by (simp add: conv_isotone mult_left_isotone)
  finally have "-(-(Datoms \<sqinter> D)\<^sup>T * Dfactor) \<le> D\<^sup>T"
    using compl_le_swap2 by blast
  thus ?thesis
    using Dsupport_def symmetric_quotient_def inf.coboundedI2 by auto
qed

lemma div_support_univalent:
  assumes "D1_reflexive _"
      and "D2_antisymmetric _"
      and "D3_transitive _"
      and "D7_pre_f_decomposable _"
      and "D8_fibered _"
      and "D9_f_decomposable _"
      and "D11_atomic _"
    shows "univalent Dsupport"
  by (metis assms div_f_decomposable_char_2 Dsupport_def syq_comp_transitive syq_converse)

lemma div_support_mapping:
  assumes "D1_reflexive _"
      and "D2_antisymmetric _"
      and "D3_transitive _"
      and "D7_pre_f_decomposable _"
      and "D8_fibered _"
      and "D9_f_decomposable _"
      and "D11_atomic _"
      and "D13_supportable _"
    shows "mapping Dsupport"
  by (simp add: assms div_support_univalent)

lemma div_support_2:
  assumes "D2_antisymmetric _"
      and "D3_transitive _"
      and "D9_f_decomposable _"
      and "D11_atomic _"
    shows "Dsupport = -((Datoms \<sqinter> D)\<^sup>T * -Dfactor) \<sqinter> -(-D\<^sup>T * (Datoms \<sqinter> D))"
proof (rule order.antisym)
  have "-D\<^sup>T * (Datoms \<sqinter> D) \<le> -D\<^sup>T * D * Dfactor"
    by (simp add: assms(3) comp_associative mult_right_isotone)
  also have "... \<le> -(Datoms \<sqinter> D)\<^sup>T * Dfactor"
    by (meson assms(2) comp_isotone inf_le2 order.refl order_trans schroeder_6)
  finally show "Dsupport \<le> -((Datoms \<sqinter> D)\<^sup>T * -Dfactor) \<sqinter> -(-D\<^sup>T * (Datoms \<sqinter> D))"
    using Dsupport_def symmetric_quotient_def comp_inf.mult_right_isotone by auto
  have "D \<sqinter> Dfactor * Dfactor\<^sup>T \<le> D\<^sup>T"
    using Dfactor_def maximal_comparable by auto
  hence "Datoms \<sqinter> D \<sqinter> Dfactor * Dfactor\<^sup>T \<le> Datoms \<sqinter> D \<sqinter> D\<^sup>T"
    by (simp add: inf.coboundedI2 inf.sup_monoid.add_assoc)
  also have "... \<le> Datoms\<^sup>T"
    by (smt (verit, ccfv_threshold) assms(1) comp_inf.covector_comp_inf comp_inf.mult_left_isotone inf_commute inf_top.left_neutral le_inf_iff one_inf_conv)
  finally have "Dfactor * Dfactor\<^sup>T \<le> Datoms\<^sup>T \<squnion> -D \<squnion> -Datoms"
    by (simp add: heyting.implies_galois_var sup.left_commute sup_monoid.add_commute)
  hence "Dfactor\<^sup>T * -(Datoms\<^sup>T \<squnion> -D \<squnion> -Datoms)\<^sup>T \<le> -Dfactor\<^sup>T"
    using schroeder_5 by auto
  hence 1: "Dfactor\<^sup>T * (-Datoms \<sqinter> D\<^sup>T \<sqinter> Datoms\<^sup>T) \<le> -Dfactor\<^sup>T"
    by (simp add: conv_complement conv_dist_sup)
  have "Dfactor\<^sup>T * (-Datoms \<sqinter> D\<^sup>T * (Datoms \<sqinter> D)) = Dfactor\<^sup>T * (-Datoms \<sqinter> D\<^sup>T \<sqinter> Datoms\<^sup>T) * (Datoms \<sqinter> D)"
    by (metis div_atoms_vector covector_inf_comp_2 vector_complement_closed vector_inf_comp mult_assoc)
  also have "... \<le> -Dfactor\<^sup>T * (Datoms \<sqinter> D)"
    using 1 mult_left_isotone by blast
  finally have 2: "Dfactor\<^sup>T * (-Datoms \<sqinter> D\<^sup>T * (Datoms \<sqinter> D)) \<le> -Dfactor\<^sup>T * (Datoms \<sqinter> D)"
    .
  have "Dfactor\<^sup>T * (-Datoms \<sqinter> D\<^sup>T * (Datoms \<sqinter> -D)) \<le> D\<^sup>T * D\<^sup>T * (Datoms \<sqinter> -D)"
    by (simp add: div_factor_div comp_associative comp_isotone conv_isotone)
  also have "... \<le> D\<^sup>T * (Datoms \<sqinter> -D)"
    by (simp add: assms(2) mult_left_isotone transitive_conv_closed)
  finally have 3: "Dfactor\<^sup>T * (-Datoms \<sqinter> D\<^sup>T * (Datoms \<sqinter> -D)) \<le> D\<^sup>T * (Datoms \<sqinter> -D)"
    .
  have "Dfactor\<^sup>T * -(Datoms \<sqinter> D) = Dfactor\<^sup>T * (-D \<sqinter> Datoms) \<squnion> Dfactor\<^sup>T * -Datoms"
    by (smt (verit, del_insts) double_compl inf_import_p mult_left_dist_sup p_dist_sup sup_monoid.add_commute)
  also have "... \<le> D\<^sup>T * (-D \<sqinter> Datoms) \<squnion> (Dfactor \<sqinter> Dmono)\<^sup>T * -Datoms"
    using div_factor_div div_factor_mono comp_inf.semiring.add_right_mono conv_order mult_left_isotone sup_right_isotone by auto
  also have "... = D\<^sup>T * (-D \<sqinter> Datoms) \<squnion> Dfactor\<^sup>T * (-Datoms \<sqinter> Dmono)"
    by (simp add: Dmono_def comp_inf_vector conv_dist_comp conv_dist_inf)
  also have "... \<le> D\<^sup>T * (-D \<sqinter> Datoms) \<squnion> Dfactor\<^sup>T * (-Datoms \<sqinter> -Dbot)"
    using assms(1) div_least_not_mono mult_right_isotone p_antitone_iff sup_right_isotone by force
  also have "... \<le> D\<^sup>T * (-D \<sqinter> Datoms) \<squnion> Dfactor\<^sup>T * (-Datoms \<sqinter> D\<^sup>T * Datoms)"
    by (simp add: assms(4))
  also have "... = D\<^sup>T * (-D \<sqinter> Datoms) \<squnion> Dfactor\<^sup>T * (-Datoms \<sqinter> D\<^sup>T * (Datoms \<sqinter> D)) \<squnion> Dfactor\<^sup>T * (-Datoms \<sqinter> D\<^sup>T * (Datoms \<sqinter> -D))"
    by (metis inf_sup_distrib1 inf_top_right mult_left_dist_sup sup_commute sup_compl_top sup_left_commute)
  also have "... \<le> D\<^sup>T * (-D \<sqinter> Datoms) \<squnion> -Dfactor\<^sup>T * (Datoms \<sqinter> D)"
    using 2 3 by (smt (verit, best) comp_inf.semiring.add_right_mono inf.sup_monoid.add_commute sup_absorb2 sup_commute sup_monoid.add_assoc)
  also have "... = -Dfactor\<^sup>T * (Datoms \<sqinter> D) \<squnion> (Datoms \<sqinter> D)\<^sup>T * -D"
    by (simp add: div_atoms_vector conv_dist_inf covector_inf_comp_3 inf_commute sup_commute)
  finally have "Dfactor\<^sup>T * -(Datoms \<sqinter> D) \<le> -Dfactor\<^sup>T * (Datoms \<sqinter> D) \<squnion> (Datoms \<sqinter> D)\<^sup>T * -D"
    .
  hence "-(Datoms \<sqinter> D)\<^sup>T * Dfactor \<le> (Datoms \<sqinter> D)\<^sup>T * -Dfactor \<squnion> -D\<^sup>T * (Datoms \<sqinter> D)"
    by (smt (verit, best) conv_complement conv_dist_comp conv_dist_sup conv_involutive conv_order)
  hence "-((Datoms \<sqinter> D)\<^sup>T * -Dfactor) \<sqinter> -(-D\<^sup>T * (Datoms \<sqinter> D)) \<le> -(-(Datoms \<sqinter> D)\<^sup>T * Dfactor)"
    using brouwer.p_antitone by fastforce
  thus "-((Datoms \<sqinter> D)\<^sup>T * -Dfactor) \<sqinter> -(-D\<^sup>T * (Datoms \<sqinter> D)) \<le> Dsupport"
    using Dsupport_def symmetric_quotient_def by simp
qed

lemma noyau_div_support:
  assumes "D1_reflexive _"
      and "D2_antisymmetric _"
      and "D3_transitive _"
      and "D7_pre_f_decomposable _"
      and "D8_fibered _"
      and "D9_f_decomposable _"
      and "D11_atomic _"
      and "D13_supportable _"
    shows "noyau (Datoms \<sqinter> D) = Dsupport * Dsupport\<^sup>T"
  using assms div_support_mapping Dsupport_def syq_comp_syq_top syq_converse by auto

lemma div_support_transitive:
  assumes "D1_reflexive _"
      and "D2_antisymmetric _"
      and "D3_transitive _"
      and "D7_pre_f_decomposable _"
      and "D8_fibered _"
      and "D9_f_decomposable _"
      and "D11_atomic _"
      and "D13_supportable _"
    shows "idempotent Dsupport"
proof -
  let ?r = "Datoms \<sqinter> D"
  let ?s = "Datoms \<sqinter> Dfactor"
  have "?r * -(?r\<^sup>T * -?s) * -(?r\<^sup>T * -?s) \<le> ?s * -(?r\<^sup>T * -?s)"
    by (metis complement_conv_sub conv_complement mult_left_isotone schroeder_5)
  also have "... \<le> ?r * -(?r\<^sup>T * -?s)"
    by (simp add: div_factor_div le_infI2 mult_left_isotone)
  also have "... \<le> ?s"
    using pp_increasing schroeder_3 by blast
  finally have "-(?r\<^sup>T * -?s) * -(?r\<^sup>T * -?s) \<le> -(?r\<^sup>T * -?s)"
    by (simp add: p_antitone_iff schroeder_3_p mult_assoc)
  hence 1: "-(?r\<^sup>T * -Dfactor) * -(?r\<^sup>T * -Dfactor) \<le> -(?r\<^sup>T * -Dfactor)"
    by (simp add: div_atoms_vector conv_dist_inf covector_inf_comp_3 inf.sup_monoid.add_commute)
  have "-(-?r\<^sup>T * ?r) * -(-?r\<^sup>T * ?r) * ?r\<^sup>T \<le> -(-?r\<^sup>T * ?r) * ?r\<^sup>T"
    by (metis complement_conv_sub double_compl mult_right_isotone mult_assoc)
  also have "... \<le> ?r\<^sup>T"
    using brouwer.pp_increasing complement_conv_sub inf.order_trans by blast
  finally have "-(-?r\<^sup>T * ?r) * -(-?r\<^sup>T * ?r) \<le> -(-?r\<^sup>T * ?r)"
    by (simp add: p_antitone_iff schroeder_4_p)
  hence 2: "-(-D\<^sup>T * ?r) * -(-D\<^sup>T * ?r) \<le> -(-D\<^sup>T * ?r)"
    by (smt (verit, del_insts) div_atoms_vector conv_dist_inf covector_inf_comp_3 inf.sup_monoid.add_commute inf_import_p)
  have "Dsupport * Dsupport \<le> -(?r\<^sup>T * -Dfactor) * -(?r\<^sup>T * -Dfactor) \<sqinter> -(-D\<^sup>T * ?r) * -(-D\<^sup>T * ?r)"
    by (simp add: assms(2,3,6,7) div_support_2 mult_isotone)
  also have "... \<le> Dsupport"
    using 1 2 assms(2,3,6,7) div_support_2 inf.sup_mono by auto
  finally have "transitive Dsupport"
    .
  thus ?thesis
    using assms div_support_mapping transitive_mapping_idempotent by blast
qed

lemma div_support_below_noyau:
  assumes "D2_antisymmetric _"
      and "D3_transitive _"
      and "D9_f_decomposable _"
      and "D11_atomic _"
    shows "Dsupport \<le> noyau (Datoms \<sqinter> D)"
proof -
  have "-((Datoms \<sqinter> D)\<^sup>T * -Dfactor) \<le> -((Datoms \<sqinter> D)\<^sup>T * -D)"
    by (simp add: div_factor_div mult_right_isotone)
  also have "... = -((Datoms \<sqinter> D)\<^sup>T * -(Datoms \<sqinter> D))"
    by (smt (verit, ccfv_threshold) div_atoms_vector comp_inf_vector conv_dist_comp conv_dist_inf inf_commute inf_import_p symmetric_top_closed)
  finally have 1: "-((Datoms \<sqinter> D)\<^sup>T * -Dfactor) \<le> -((Datoms \<sqinter> D)\<^sup>T * -(Datoms \<sqinter> D))"
    .
  have "-(-D\<^sup>T * (Datoms \<sqinter> D)) = -(-(Datoms \<sqinter> D)\<^sup>T * (Datoms \<sqinter> D))"
    by (smt (verit, ccfv_threshold) div_atoms_vector comp_inf_vector conv_dist_comp conv_dist_inf inf_commute inf_import_p symmetric_top_closed)
  thus "Dsupport \<le> noyau (Datoms \<sqinter> D)"
    using 1 assms div_support_2 symmetric_quotient_def inf.sup_left_isotone by auto
qed

lemma div_support_least_noyau:
  assumes "D1_reflexive _"
      and "D2_antisymmetric _"
      and "D3_transitive _"
      and "D7_pre_f_decomposable _"
      and "D8_fibered _"
      and "D9_f_decomposable _"
      and "D11_atomic _"
      and "D13_supportable _"
    shows "Dsupport = (least D (noyau (Datoms \<sqinter> D)))\<^sup>T"
proof (rule order.antisym)
  let ?n = "noyau (Datoms \<sqinter> D)"
  have "?n \<le> Dsupport * D"
    by (metis assms div_support_div conv_involutive conv_order mult_right_isotone noyau_div_support)
  hence "Dsupport\<^sup>T * ?n \<le> D"
    using assms div_support_mapping shunt_mapping by blast
  hence "Dsupport \<le> -(?n * -D\<^sup>T)"
    by (simp add: compl_le_swap1 conv_complement schroeder_6_p)
  hence "Dsupport \<le> -(-D * ?n)\<^sup>T"
    by (simp add: conv_complement conv_dist_comp syq_converse)
  thus "Dsupport \<le> (least D ?n)\<^sup>T"
    using assms(2,3,6,7) div_support_below_noyau least_def syq_converse conv_complement conv_dist_inf by auto
  have "Dsupport \<sqinter> -1 \<le> (Dsupport \<sqinter> -1) * (Dsupport \<sqinter> -1)\<^sup>T * (Dsupport \<sqinter> -1)"
    using ex231c by auto
  also have "... \<le> (D\<^sup>T \<sqinter> -1) * Dsupport\<^sup>T * Dsupport"
    using assms(1-7) div_support_div comp_inf.mult_left_isotone comp_isotone conv_order by auto
  also have "... \<le> -D * Dsupport"
    by (metis assms div_antisymmetric_equal div_support_mapping div_support_transitive inf_commute mult_isotone order_refl p_shunting_swap pp_increasing shunt_mapping mult_assoc)
  finally have 1: "least D Dsupport \<le> 1"
    by (metis double_compl least_def p_shunting_swap)
  have "least D ?n = Dsupport * Dsupport\<^sup>T \<sqinter> -(-D * Dsupport * Dsupport\<^sup>T)"
    by (simp add: assms comp_associative least_def noyau_div_support)
  also have "... = (Dsupport \<sqinter> -(-D * Dsupport)) * Dsupport\<^sup>T"
    using assms div_support_univalent comp_bijective_complement injective_comp_right_dist_inf total_conv_surjective by auto
  also have "... \<le> Dsupport\<^sup>T"
    using 1 least_def mult_left_isotone by fastforce
  finally show "(least D ?n)\<^sup>T \<le> Dsupport"
    using conv_order by fastforce
qed

lemma div_factor_support:
  assumes "D13_supportable _"
    shows "Datoms \<sqinter> D = Dfactor * Dsupport\<^sup>T"
  by (metis assms Dsupport_def comp_syq_top inf.sup_monoid.add_commute inf_top.left_neutral surjective_conv_total syq_converse)

lemma div_supportable_iff:
  assumes "D2_antisymmetric _"
      and "D6_least_surjective _"
    shows "D13_supportable _ \<longleftrightarrow> Datoms \<sqinter> D = Dfactor * Dsupport\<^sup>T"
  by (metis assms Dsupport_def div_total_top_factor comp_syq_surjective conv_dist_comp symmetric_top_closed syq_converse)

subsection \<open>Increments\<close>

lemma least_div_atoms_succ:
  "Dbot \<sqinter> Datoms\<^sup>T \<le> Dsucc"
proof -
  have 1: "Dbot \<sqinter> Datoms\<^sup>T \<le> D"
    using div_least_div inf.coboundedI1 by blast
  have 2: "Dbot \<sqinter> Datoms\<^sup>T \<le> -1"
    by (metis div_least_not_atom comp_inf.semiring.mult_not_zero inf.sup_monoid.add_assoc inf.sup_monoid.add_commute one_inf_conv pseudo_complement)
  have "(D \<sqinter> -1)\<^sup>T * -Dbot \<le> -Datoms"
    by (simp add: Datoms_def minimal_def conv_complement conv_dist_inf)
  hence "(D \<sqinter> -1) * Datoms \<le> Dbot"
    by (simp add: schroeder_3_p)
  hence "(D \<sqinter> -1) * Datoms * Dbot\<^sup>T \<le> Dbot"
    by (metis div_least_vector mult_isotone top_greatest)
  also have "... \<le> D"
    by (simp add: div_least_div)
  finally have "Dbot * Datoms\<^sup>T \<le> -(-D\<^sup>T * (D \<sqinter> -1))"
    by (metis comp_associative compl_le_swap1 conv_dist_comp conv_involutive schroeder_6)
  hence "Dbot \<sqinter> Datoms\<^sup>T \<le> -(-D\<^sup>T * (D \<sqinter> -1))"
    by (simp add: div_atoms_vector div_least_vector vector_covector)
  thus ?thesis
    using 1 2 Dsucc_def greatest_def by auto
qed

lemma least_div_succ:
  assumes "D12_infinite_base _"
    shows "Dbot \<le> Dsucc * top"
proof -
  have "Dbot \<le> (Dbot \<sqinter> Datoms\<^sup>T) * top"
    using assms div_atom_surjective div_least_vector surjective_conv_total vector_inf_comp by auto
  also have "... \<le> Dsucc * top"
    using least_div_atoms_succ mult_left_isotone by blast
  finally show ?thesis
    .
qed

lemma noyau_div:
  assumes "D1_reflexive _"
      and "D2_antisymmetric _"
    shows "noyau D = 1"
  by (simp add: assms reflexive_antisymmetric_noyau)

lemma div_discrete_fibers_pred_geq:
  assumes "D1_reflexive _"
      and "D2_antisymmetric _"
      and "D3_transitive _"
      and "D7_pre_f_decomposable _"
      and "D8_fibered _"
      and "D9_f_decomposable _"
      and "D11_atomic _"
    shows "Dsucc\<^sup>T * top \<le> Dmono"
proof -
  have "Dfactor \<sqinter> -Dmono\<^sup>T \<le> -1"
    by (metis brouwer.p_antitone conv_complement div_factor_mono inf.coboundedI2 inf_commute one_inf_conv p_shunting_swap)
  hence "Dfactor \<sqinter> -Dmono\<^sup>T \<le> D \<sqinter> -1"
    by (simp add: div_factor_div le_infI1)
  hence "Dsucc \<le> D \<sqinter> -1 \<sqinter> -(-D\<^sup>T * (Dfactor \<sqinter> -Dmono\<^sup>T))"
    by (metis Dsucc_def greatest_def inf.sup_right_isotone mult_right_isotone p_antitone)
  also have "... = D \<sqinter> -1 \<sqinter> -(-D\<^sup>T * Dfactor \<sqinter> -Dmono\<^sup>T)"
    by (simp add: covector_comp_inf div_mono_vector vector_conv_compl)
  also have "... = (D \<sqinter> -1 \<sqinter> -(-D\<^sup>T * Dfactor)) \<squnion> (D \<sqinter> -1 \<sqinter> Dmono\<^sup>T)"
    by (simp add: comp_inf.semiring.distrib_left)
  also have "... = (D \<sqinter> -1 \<sqinter> D\<^sup>T) \<squnion> (D \<sqinter> -1 \<sqinter> Dmono\<^sup>T)"
    by (metis assms div_f_decomposable_char_1 conv_complement conv_dist_comp conv_involutive double_compl)
  also have "... = D \<sqinter> -1 \<sqinter> Dmono\<^sup>T"
    using assms(1,2) div_antisymmetric_equal inf_commute by fastforce
  also have "... \<le> Dmono\<^sup>T"
    by simp
  finally show ?thesis
    by (metis conv_involutive conv_order div_mono_vector mult_left_isotone)
qed

lemma div_discrete_fibers_pred_eq:
  assumes "D1_reflexive _"
      and "D2_antisymmetric _"
      and "D3_transitive _"
      and "D7_pre_f_decomposable _"
      and "D8_fibered _"
      and "D9_f_decomposable _"
      and "D11_atomic _"
      and "D15b_discrete_fibers_pred _"
    shows "Dmono = Dsucc\<^sup>T * top"
  by (simp add: assms div_discrete_fibers_pred_geq dual_order.eq_iff)

lemma div_discrete_fibers_pred_iff:
  assumes "D1_reflexive _"
      and "D2_antisymmetric _"
      and "D3_transitive _"
      and "D7_pre_f_decomposable _"
      and "D8_fibered _"
      and "D9_f_decomposable _"
      and "D11_atomic _"
    shows "D15b_discrete_fibers_pred _ \<longleftrightarrow> Dmono = Dsucc\<^sup>T * top"
  using assms div_discrete_fibers_pred_geq by force

lemma div_succ_univalent:
  assumes "D1_reflexive _"
      and "D2_antisymmetric _"
      and "D3_transitive _"
      and "D7_pre_f_decomposable _"
      and "D8_fibered _"
      and "D9_f_decomposable _"
      and "D11_atomic _"
      and "D15b_discrete_fibers_pred _"
    shows "Dsucc\<^sup>T * (-Dbot \<sqinter> Dsucc) \<le> 1"
proof -
  have 1: "Dsucc \<le> D"
    by (simp add: Dsucc_def greatest_def inf_assoc)
  have 2: "D\<^sup>T * Datoms \<sqinter> D \<le> D\<^sup>T * (Datoms \<sqinter> D)"
    using assms(3,7) div_via_atom comp_inf.coreflexive_commutative by auto
  have 3: "(D \<sqinter> -1) * Dsucc\<^sup>T \<le> D"
    by (metis Dsucc_def conv_involutive double_compl greatest_def p_dist_sup schroeder_6 sup.cobounded2)
  have "Dsucc\<^sup>T * Dsucc \<sqinter> D \<sqinter> -1 \<le> (Dsucc\<^sup>T \<sqinter> (D \<sqinter> -1) * Dsucc\<^sup>T) * Dsucc"
    by (simp add: comp_inf.vector_inf_comp dedekind_2)
  also have "... \<le> (Dsucc\<^sup>T \<sqinter> D) * Dsucc"
    using 3 inf.sup_right_isotone mult_left_isotone by blast
  also have "... \<le> ((D \<sqinter> -1)\<^sup>T \<sqinter> D) * Dsucc"
    using Dsucc_def conv_dist_inf greatest_def inf.cobounded1 inf.sup_left_isotone mult_left_isotone by auto
  also have "... = bot"
    by (metis assms(2) antisymmetric_inf_diversity conv_inf_bot_iff equivalence_one_closed inf_compl_bot_right mult_1_right mult_left_zero schroeder_2)
  finally have 4: "Dsucc\<^sup>T * Dsucc \<sqinter> D \<le> 1"
    by (simp add: shunting_1)
  hence 5: "Dsucc\<^sup>T * Dsucc \<sqinter> D\<^sup>T \<le> 1"
    by (metis conv_dist_comp conv_dist_inf conv_involutive coreflexive_symmetric)
  have "Dsucc\<^sup>T * (-Dbot \<sqinter> Dsucc) \<le> top * Dsucc"
    by (simp add: mult_isotone)
  also have "... = Dmono\<^sup>T"
    using assms div_discrete_fibers_pred_eq conv_dist_comp by fastforce
  finally have "Dsucc\<^sup>T * (-Dbot \<sqinter> Dsucc) = Dsucc\<^sup>T * (-Dbot \<sqinter> Dsucc) \<sqinter> Dmono\<^sup>T"
    using inf.order_iff by auto
  also have "... = Dmono \<sqinter> Dsucc\<^sup>T * (-Dbot \<sqinter> Dsucc) \<sqinter> Dmono\<^sup>T"
    by (metis assms div_discrete_fibers_pred_eq div_mono_vector domain_comp vector_export_comp_unit vector_inf_comp)
  also have "... \<le> Dmono \<sqinter> D\<^sup>T * (-Dbot \<sqinter> D) \<sqinter> Dmono\<^sup>T"
    using 1 conv_order inf.sup_left_isotone inf.sup_right_isotone mult_isotone by auto
  also have "... = Dmono \<sqinter> D\<^sup>T * (D\<^sup>T * Datoms \<sqinter> D) \<sqinter> Dmono\<^sup>T"
    using assms(7) by auto
  also have "... \<le> Dmono \<sqinter> D\<^sup>T * D\<^sup>T * (Datoms \<sqinter> D) \<sqinter> Dmono\<^sup>T"
    using 2 by (metis comp_inf.mult_left_isotone inf_commute mult_right_isotone mult_assoc)
  also have "... = Dmono \<sqinter> D\<^sup>T * (Datoms \<sqinter> D) \<sqinter> Dmono\<^sup>T"
    by (metis assms(1,3) div_idempotent conv_dist_comp)
  also have "... \<le> D \<squnion> D\<^sup>T"
    using assms(5) by force
  finally have "Dsucc\<^sup>T * (-Dbot \<sqinter> Dsucc) = Dsucc\<^sup>T * (-Dbot \<sqinter> Dsucc) \<sqinter> (D \<squnion> D\<^sup>T)"
    using inf.absorb1 by auto
  also have "... \<le> Dsucc\<^sup>T * Dsucc \<sqinter> (D \<squnion> D\<^sup>T)"
    using comp_inf.mult_left_isotone comp_isotone by force
  also have "... = (Dsucc\<^sup>T * Dsucc \<sqinter> D) \<squnion> (Dsucc\<^sup>T * Dsucc \<sqinter> D\<^sup>T)"
    using inf_sup_distrib1 by blast
  also have "... \<le> 1"
    using 4 5 le_sup_iff by blast
  finally show ?thesis
    .
qed

lemma div_succ_injective:
  assumes "D2_antisymmetric _"
    shows "injective Dsucc"
  by (simp add: assms Dsucc_def greatest_injective)

lemma div_succ_below_div_irreflexive:
  "Dsucc \<le> D \<sqinter> -1"
  by (metis Dsucc_def greatest_def inf_le1)

lemma div_succ_below_div:
  "Dsucc \<le> D"
  using div_succ_below_div_irreflexive by auto

lemma div_succ_mono_bot:
  assumes "D1_reflexive _"
      and "D2_antisymmetric _"
      and "D3_transitive _"
      and "D7_pre_f_decomposable _"
      and "D8_fibered _"
      and "D9_f_decomposable _"
      and "D11_atomic _"
      and "D12_infinite_base _"
      and "D15a_discrete_fibers_succ _"
    shows "Dsucc * top = Dmonobot"
proof -
  have "Dsucc * top \<le> Dsucc * Dsucc\<^sup>T * Dsucc * top"
    by (simp add: comp_isotone ex231c)
  also have "... \<le> Dsucc * Dsucc\<^sup>T * top"
    by (simp add: mult_right_isotone mult_assoc)
  also have "... \<le> Dsucc * Dmono"
    by (simp add: assms div_discrete_fibers_pred_geq mult_right_isotone mult_assoc)
  also have "... \<le> D * Dmono"
    using div_succ_below_div mult_left_isotone by auto
  also have "... \<le> Dmonobot"
    using assms(3,7) div_mono_downclosed Dmonobot_def heyting.implies_galois_var sup_commute by auto
  finally have "Dsucc * top \<le> Dmonobot"
    .
  thus ?thesis
    by (simp add: assms(8,9) least_div_succ Dmonobot_def order.antisym)
qed

lemma div_discrete_fibers_succ_iff:
  assumes "D1_reflexive _"
      and "D2_antisymmetric _"
      and "D3_transitive _"
      and "D7_pre_f_decomposable _"
      and "D8_fibered _"
      and "D9_f_decomposable _"
      and "D11_atomic _"
      and "D12_infinite_base _"
    shows "D15a_discrete_fibers_succ _ \<longleftrightarrow> Dsucc * top = Dmonobot"
  using Dmonobot_def assms div_succ_mono_bot by force

lemma div_succ_bot_atoms:
  assumes "D1_reflexive _"
      and "D2_antisymmetric _"
      and "D3_transitive _"
      and "D6_least_surjective _"
    shows "Dsucc\<^sup>T * Dbot = Datoms"
proof (rule order.antisym)
  have "Dsucc\<^sup>T * Dbot \<le> (D \<sqinter> -1)\<^sup>T * top"
    using div_succ_below_div_irreflexive conv_order mult_isotone by auto
  also have "... \<le> -Dbot"
    by (simp add: assms(2) div_strict_bot schroeder_3_p)
  finally have 1: "Dsucc\<^sup>T * Dbot \<le> -Dbot"
    .
  have "-Dbot * Dbot\<^sup>T \<le> -D"
    by (metis assms(1,3) bot_div_bot complement_conv_sub)
  hence "(D \<sqinter> -1)\<^sup>T * -Dbot * Dbot\<^sup>T \<le> (D \<sqinter> -1)\<^sup>T * -D"
    by (simp add: comp_isotone mult_assoc)
  hence 2: "-((D \<sqinter> -1)\<^sup>T * -D) * Dbot \<le> -((D \<sqinter> -1)\<^sup>T * -Dbot)"
    by (simp add: schroeder_4_p)
  have "Dsucc \<le> -(-D\<^sup>T * (D \<sqinter> -1))"
    by (simp add: Dsucc_def greatest_def)
  hence "Dsucc\<^sup>T \<le> -((D \<sqinter> -1)\<^sup>T * -D)"
    by (simp add: Dsucc_def conv_complement conv_dist_comp conv_dist_inf greatest_def)
  hence "Dsucc\<^sup>T * Dbot \<le> -((D \<sqinter> -1)\<^sup>T * -D) * Dbot"
    using mult_left_isotone by blast
  also have "... \<le> -((D \<sqinter> -1)\<^sup>T * -Dbot)"
    using 2 by blast
  finally show "Dsucc\<^sup>T * Dbot \<le> Datoms"
    using 1 by (simp add: Datoms_def conv_complement conv_dist_inf minimal_def)
  have "Datoms * Dbot\<^sup>T \<le> Dsucc\<^sup>T"
    by (metis div_atoms_vector least_div_atoms_succ double_compl schroeder_3_p schroeder_5 vector_covector div_least_vector)
  thus "Datoms \<le> Dsucc\<^sup>T * Dbot"
    using assms(2,4) div_least_point shunt_bijective by blast
qed

lemma div_succ_inverse_poly:
  assumes "D1_reflexive _"
      and "D2_antisymmetric _"
      and "D3_transitive _"
      and "D6_least_surjective _"
      and "D7_pre_f_decomposable _"
      and "D8_fibered _"
      and "D9_f_decomposable _"
      and "D11_atomic _"
      and "D15b_discrete_fibers_pred _"
    shows "Dsucc\<^sup>T * Dsucc * (Dmono \<sqinter> -Datoms \<sqinter> 1) = Dmono \<sqinter> -Datoms \<sqinter> 1"
proof (rule order.antisym)
  let ?q = "Dmono \<sqinter> -Datoms \<sqinter> 1"
  have "?q = ?q \<sqinter> Dsucc\<^sup>T * top"
    using assms(1-3,5-9) div_discrete_fibers_pred_eq inf_commute inf_left_commute by auto
  also have "... = ?q \<sqinter> (Dsucc\<^sup>T \<sqinter> ?q * top) * (top \<sqinter> Dsucc * ?q)"
    by (simp add: dedekind_eq inf.sup_monoid.add_commute)
  also have "... \<le> Dsucc\<^sup>T * Dsucc * ?q"
    using comp_associative inf.coboundedI2 inf_vector_comp by auto
  finally show "?q \<le> Dsucc\<^sup>T * Dsucc * ?q"
    .
  have "Dsucc * ?q \<le> Dsucc * -Datoms"
    by (simp add: inf.coboundedI1 mult_right_isotone)
  also have "... \<le> -Dbot"
    by (metis assms(1-4) div_succ_bot_atoms conv_complement_sub_leq conv_involutive)
  finally have "Dsucc\<^sup>T * Dsucc * ?q = Dsucc\<^sup>T * (-Dbot \<sqinter> Dsucc * ?q)"
    by (simp add: inf.le_iff_sup mult_assoc)
  also have "... = Dsucc\<^sup>T * (-Dbot \<sqinter> Dsucc) * ?q"
    by (simp add: Dbot_def comp_associative least_def vector_export_comp)
  also have "... \<le> ?q"
    by (metis assms(1-3,5-9) div_succ_univalent coreflexive_comp_inf inf.sup_right_divisibility)
  finally show "Dsucc\<^sup>T * Dsucc * ?q \<le> ?q"
    .
qed

lemma div_inc_injective:
  assumes "D1_reflexive _"
      and "D2_antisymmetric _"
      and "D3_transitive _"
      and "D7_pre_f_decomposable _"
      and "D8_fibered _"
      and "D9_f_decomposable _"
      and "D11_atomic _"
    shows "injective Dinc"
  using assms div_f_decomposable_char_2 Dinc_def syq_comp_top_syq syq_converse by force

lemma div_factor_not_bot:
  assumes "D2_antisymmetric _"
    shows "Dfactor \<le> -Dbot"
  using assms div_factor_mono div_least_not_mono compl_le_swap1 inf.order_trans by blast

lemma div_factor_conv_inc:
  assumes "D1_reflexive _"
      and "D2_antisymmetric _"
      and "D3_transitive _"
      and "D6_least_surjective _"
    shows "Dfactor * Dinc\<^sup>T \<le> Dmono \<sqinter> -Datoms"
proof -
  have 1: "Dfactor * Dinc\<^sup>T \<le> Dmono"
    by (metis div_factor_mono div_mono_vector mult_isotone top_greatest)
  have "Dfactor * Dinc\<^sup>T = Dfactor * symmetric_quotient (Dsucc * Dfactor) Dfactor"
    by (simp add: Dinc_def syq_converse)
  also have "... \<le> Dfactor * -((Dsucc * Dfactor)\<^sup>T * -Dfactor)"
    using mult_right_isotone symmetric_quotient_def by force
  also have "... \<le> Dfactor * -((Dsucc * Dfactor)\<^sup>T * Dbot)"
    using assms(2) div_factor_not_bot mult_right_isotone p_antitone_iff by auto
  also have "... = Dfactor * -(Dfactor\<^sup>T * Datoms)"
    by (simp add: assms div_succ_bot_atoms conv_dist_comp mult_assoc)
  also have "... \<le> -Datoms"
    by (simp add: schroeder_3)
  finally show ?thesis
    using 1 by auto
qed

lemma div_inc_univalent:
  assumes "D1_reflexive _"
      and "D2_antisymmetric _"
      and "D3_transitive _"
      and "D6_least_surjective _"
      and "D7_pre_f_decomposable _"
      and "D8_fibered _"
      and "D9_f_decomposable _"
      and "D11_atomic _"
      and "D15b_discrete_fibers_pred _"
    shows "univalent Dinc"
proof -
  let ?sf = "Dsucc * Dfactor"
  let ?p = "symmetric_quotient ?sf Dfactor * top \<sqinter> 1"
  let ?q = "Dmono \<sqinter> -Datoms \<sqinter> 1"
  have "Dfactor * ?p \<le> Dfactor * Dinc\<^sup>T * top"
    by (simp add: Dinc_def mult_right_isotone syq_converse mult_assoc)
  also have "... \<le> Dmono \<sqinter> -Datoms"
    by (metis assms(1-4) div_atoms_vector div_factor_conv_inc Dmono_def mult_left_isotone vector_complement_closed vector_export_comp)
  finally have "Dfactor * ?p \<le> ?q * Dfactor * ?p"
    by (smt (verit, ccfv_threshold) div_atoms_vector div_mono_vector complement_vector inf.le_sup_iff mult_left_one order_refl vector_inf_comp)
  hence "Dfactor * ?p = ?q * Dfactor * ?p"
    by (simp add: inf.absorb2 test_comp_test_inf)
  hence 1: "Dsucc\<^sup>T * ?sf * ?p = Dfactor * ?p"
    by (metis assms div_succ_inverse_poly mult_assoc)
  have "Dinc\<^sup>T * Dinc = symmetric_quotient ?sf Dfactor * symmetric_quotient Dfactor ?sf"
    by (simp add: Dinc_def syq_converse)
  also have "... = symmetric_quotient ?sf Dfactor * top \<sqinter> symmetric_quotient ?sf ?sf \<sqinter> top * symmetric_quotient Dfactor ?sf"
    by (smt (verit) comp_isotone inf.absorb_iff2 inf.sup_monoid.add_assoc order.refl syq_comp_top_syq top.extremum)
  also have "... = ?p * symmetric_quotient ?sf ?sf \<sqinter> top * symmetric_quotient Dfactor ?sf"
    using vector_export_comp_unit by auto
  also have "... = ?p * symmetric_quotient ?sf ?sf * ?p"
    by (simp add: comp_inf_vector inf_commute syq_converse)
  also have "... = ?p * symmetric_quotient (?sf * ?p) (?sf * ?p) * ?p"
    using coreflexive_comp_syq_comp_coreflexive inf_le2 by blast
  also have "... \<le> ?p * symmetric_quotient (Dsucc\<^sup>T * ?sf * ?p) (Dsucc\<^sup>T * ?sf * ?p) * ?p"
    using comp_isotone order.refl syq_comp_isotone mult_assoc by auto
  also have "... = ?p * symmetric_quotient (Dfactor * ?p) (Dfactor * ?p) * ?p"
    using 1 by auto
  also have "... = ?p * symmetric_quotient Dfactor Dfactor * ?p"
    by (metis coreflexive_comp_syq_comp_coreflexive inf.cobounded2)
  also have "... \<le> symmetric_quotient Dfactor Dfactor"
    by (simp add: assms(1-3,5-8) div_f_decomposable_char_2 vector_export_comp_unit)
  also have "... = 1"
    using assms(1-3,5-8) div_f_decomposable_char_2 by blast
  finally show ?thesis
    .
qed

lemma div_inc_mapping:
  assumes "D1_reflexive _"
      and "D2_antisymmetric _"
      and "D3_transitive _"
      and "D6_least_surjective _"
      and "D7_pre_f_decomposable _"
      and "D8_fibered _"
      and "D9_f_decomposable _"
      and "D11_atomic _"
      and "D15b_discrete_fibers_pred _"
      and "D16_incrementable _"
    shows "mapping Dinc"
  using assms div_inc_univalent by blast

lemma div_inc_mapping:
  assumes "D1_reflexive _"
      and "D2_antisymmetric _"
      and "D3_transitive _"
      and "D6_least_surjective _"
      and "D7_pre_f_decomposable _"
      and "D8_fibered _"
      and "D9_f_decomposable _"
      and "D11_atomic _"
      and "D13_supportable _"
      and "D15a_discrete_fibers_succ _"
      and "D15b_discrete_fibers_pred _"
      and "D16_incrementable _"
    shows "surjective Datoms"
  nitpick[expect=genuine,card=2]
  oops

end

end
