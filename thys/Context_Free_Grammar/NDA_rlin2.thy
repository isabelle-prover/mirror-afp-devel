(*
Authors: Kaan Taskin, Tobias Nipkow
*)

section \<open>Strongly Right-Linear Grammars as a Nondeterministic Automaton\<close>

theory NDA_rlin2
imports Right_Linear
begin

text
\<open>We define what is essentially the extended transition function of a nondeterministic automaton
but is driven by a set of strongly right-linear productions \<open>P\<close>, which are of course
just another representation of the transitions of a nondeterministic automaton.
Function \<open>nxts_rlin2_set P M w\<close> traverses the terminals list \<open>w\<close>
starting from the set of non-terminals \<open>M\<close> according to the productions of \<open>P\<close>.
At the end it returns the reachable non-terminals.\<close>

definition nxt_rlin2 :: "('n,'t)Prods \<Rightarrow> 'n \<Rightarrow> 't \<Rightarrow> 'n set" where
"nxt_rlin2 P A a = {B. (A, [Tm a, Nt B]) \<in> P}"

definition nxt_rlin2_set :: "('n,'t)Prods \<Rightarrow> 'n set \<Rightarrow> 't \<Rightarrow> 'n set" where
"nxt_rlin2_set P M a = (\<Union>A\<in>M. nxt_rlin2 P A a)"

definition nxts_rlin2_set :: "('n,'t)Prods \<Rightarrow> 'n set \<Rightarrow> 't list \<Rightarrow> 'n set" where
"nxts_rlin2_set P = foldl (nxt_rlin2_set P)"

lemma nxt_rlin2_nts:
  assumes "B\<in>nxt_rlin2 P A a"
  shows "B\<in>Nts P"
  using assms nxt_rlin2_def Nts_def nts_syms_def by fastforce

lemma nxts_rlin2_set_app: 
  "nxts_rlin2_set P M (x @ y) = nxts_rlin2_set P (nxts_rlin2_set P M x) y"
  unfolding nxts_rlin2_set_def by simp

lemma nxt_rlin2_set_pick:
  assumes "B \<in> nxt_rlin2_set P M a"
  shows   "\<exists>C\<in>M. B \<in> nxt_rlin2_set P {C} a"
  using assms by (simp add:nxt_rlin2_def nxt_rlin2_set_def)

lemma nxts_rlin2_set_pick:
  assumes "B \<in> nxts_rlin2_set P M w"
  shows "\<exists>C\<in>M. B \<in> nxts_rlin2_set P {C} w"
using assms proof (induction w arbitrary: B rule: rev_induct)
  case Nil
  then show ?case
    by (simp add: nxts_rlin2_set_def)
next
  case (snoc x xs)
  from snoc(2) have B_in: "B \<in> nxts_rlin2_set P (nxts_rlin2_set P M xs) [x]"
    using nxts_rlin2_set_app[of P M xs "[x]"] by simp
  hence "B \<in> nxt_rlin2_set P (nxts_rlin2_set P M xs) x"
    by (simp add: nxts_rlin2_set_def)
  hence "\<exists>C\<in>(nxts_rlin2_set P M xs). B \<in> nxt_rlin2_set P {C} x"
    using nxt_rlin2_set_pick[of B P "nxts_rlin2_set P M xs" x] by simp
  then obtain C where C_def: "C \<in> nxts_rlin2_set P M xs" and C_path: "B \<in> nxt_rlin2_set P {C} x"
    by blast
  have "\<exists>Ca\<in>M. C \<in> nxts_rlin2_set P {Ca} xs"
    using snoc.IH[of C, OF C_def] .
  then obtain D where *: "D \<in> M" and D_path: "C \<in> nxts_rlin2_set P {D} xs"
    by blast
  from C_path D_path have **: "B \<in> nxts_rlin2_set P {D} (xs @ [x])"
    unfolding nxts_rlin2_set_def nxt_rlin2_set_def by auto
  from * ** show ?case by blast
qed

lemma nxts_rlin2_set_first_step:
  assumes "B \<in> nxts_rlin2_set P {A} (a # w)"
  shows "\<exists>C \<in> nxt_rlin2 P A a. B \<in> nxts_rlin2_set P {C} w"
proof -
  from assms have "B \<in> nxts_rlin2_set P {A} ([a]@w)" by simp
  hence "B \<in> nxts_rlin2_set P (nxts_rlin2_set P {A} [a]) w" 
    using nxts_rlin2_set_app[of P "{A}" "[a]" w] by simp
  hence "B \<in> nxts_rlin2_set P (nxt_rlin2 P A a) w"
    by (simp add: nxt_rlin2_set_def nxts_rlin2_set_def)
  thus "\<exists>C \<in> nxt_rlin2 P A a. B \<in> nxts_rlin2_set P {C} w"
    using nxts_rlin2_set_pick[of B P "nxt_rlin2 P A a" w] by simp
qed

lemma nxts_trans0:
  assumes "B \<in> nxts_rlin2_set P (nxts_rlin2_set P {A} x) z"
  shows "B \<in> nxts_rlin2_set P {A} (x@z)"
  by (metis assms foldl_append nxts_rlin2_set_def)

lemma nxt_mono:
  assumes "A \<subseteq> B"
  shows "nxt_rlin2_set P A a \<subseteq> nxt_rlin2_set P B a"
  unfolding nxt_rlin2_set_def using assms by blast

lemma nxts_mono:
  assumes "A \<subseteq> B"
  shows "nxts_rlin2_set P A w \<subseteq> nxts_rlin2_set P B w"
  unfolding nxts_rlin2_set_def proof (induction w rule:rev_induct)
  case Nil
  thus ?case by (simp add: assms)
next
  case (snoc x xs)
  thus  ?case 
    using nxt_mono[of "foldl (nxt_rlin2_set P) A xs" "foldl (nxt_rlin2_set P) B xs" P x] by simp
qed

lemma nxts_trans1:
  assumes "M \<subseteq> nxts_rlin2_set P {A} x"
      and "B \<in> nxts_rlin2_set P M z"
  shows "B \<in> nxts_rlin2_set P {A} (x@z)"
  using assms nxts_trans0[of B P A x z] nxts_mono[of M "nxts_rlin2_set P {A} x" P z, OF assms(1)] by auto

lemma nxts_trans2:
  assumes "C \<in> nxts_rlin2_set P {A} x"
      and "B \<in> nxts_rlin2_set P {C} z"
    shows "B \<in> nxts_rlin2_set P {A} (x@z)"
  using assms nxts_trans1[of "{C}" P A x B z] by auto

lemma nxts_to_mult_derive:
  "B \<in> nxts_rlin2_set P M w \<Longrightarrow> (\<exists>A\<in>M. P \<turnstile> [Nt A] \<Rightarrow>* map Tm w @ [Nt B])"
unfolding nxts_rlin2_set_def proof (induction w arbitrary: B rule: rev_induct)
  case Nil
  hence 1: "B \<in> M" by simp
  have 2: "P \<turnstile> [Nt B] \<Rightarrow>* map Tm [] @ [Nt B]" by simp
  from 1 2 show ?case by blast
next
  case (snoc x xs)
  from snoc.prems have "\<exists>C. C \<in> foldl (nxt_rlin2_set P) M xs \<and> (C, [Tm x, Nt B]) \<in> P"
    unfolding nxt_rlin2_set_def nxt_rlin2_def by auto
  then obtain C where C_xs: "C \<in> foldl (nxt_rlin2_set P) M xs" and C_prod: "(C, [Tm x, Nt B]) \<in> P" by blast
  from C_xs obtain A where A_der: "P \<turnstile> [Nt A] \<Rightarrow>* map Tm xs @ [Nt C]" and A_in: "A \<in> M" 
    using snoc.IH[of C] by auto
  from C_prod have "P \<turnstile> [Nt C] \<Rightarrow> [Tm x, Nt B]"
    using derive_singleton[of P "Nt C" "[Tm x, Nt B]"] by blast
  hence "P \<turnstile> map Tm xs @ [Nt C] \<Rightarrow> map Tm xs @ [Tm x, Nt B]"
    using derive_prepend[of P "[Nt C]" "[Tm x, Nt B]" "map Tm xs"] by simp
  hence C_der: "P \<turnstile> map Tm xs @ [Nt C] \<Rightarrow> map Tm (xs @ [x]) @ [Nt B]" by simp
  from A_der C_der have "P \<turnstile> [Nt A] \<Rightarrow>* map Tm (xs @ [x]) @ [Nt B]" by simp
  with A_in show ?case by blast
qed

lemma mult_derive_to_nxts:
  assumes "rlin2 P"
  shows "A\<in>M \<Longrightarrow> P \<turnstile> [Nt A] \<Rightarrow>* map Tm w @ [Nt B] \<Longrightarrow> B \<in> nxts_rlin2_set P M w"
unfolding nxts_rlin2_set_def proof (induction w arbitrary: B rule: rev_induct)
  case Nil
  with assms have "A = B"
    using rlin2_nts_derive_eq[of P A B] by simp
  with Nil.prems(1) show ?case by simp
next
  case (snoc x xs)
  from snoc.prems(2) have "P \<turnstile> [Nt A] \<Rightarrow>* map Tm xs @ [Tm x,Nt B]" by simp
  with assms obtain C where C_der: "P \<turnstile> [Nt A] \<Rightarrow>* map Tm xs @ [Nt C]"
                        and C_prods: "(C,[Tm x, Nt B]) \<in> P" using rlin2_introduce_tm[of P A xs x B] by fast
  from \<open>A \<in> M\<close> C_der have "C \<in> foldl (nxt_rlin2_set P) M xs"
    using snoc.IH[of C] by auto
  with C_prods show ?case
    unfolding nxt_rlin2_set_def nxt_rlin2_def by auto
qed

text
\<open>Acceptance of a word \<open>w\<close> w.r.t. \<open>P\<close> (starting from \<open>A\<close>), \<open>accepted P A w\<close>, means that we can reach
an ``accepting'' nonterminal \<open>Z\<close>, i.e. one with a production \<open>(Z,[])\<close>.
On the automaton level \<open>Z\<close> reachable final state.
We show that \<open>accepted P A w\<close> iff \<open>w\<close> is in the language of \<open>A\<close> w.r.t. \<open>P\<close>.\<close>

definition "accepted P A w = (\<exists>Z \<in> nxts_rlin2_set P {A} w. (Z,[]) \<in> P)"

theorem accepted_if_Lang:
  assumes "rlin2 P"
      and "w \<in> Lang P A"
    shows "accepted P A w"
proof -
  from assms obtain B where A_der: "P \<turnstile> [Nt A] \<Rightarrow>* map Tm w @ [Nt B]" and B_in: "(B,[]) \<in> P" 
    unfolding Lang_def using rlin2_tms_eps[of P A w] by auto
  from A_der have "B \<in> nxts_rlin2_set P {A} w" 
    using mult_derive_to_nxts[OF assms(1)] by auto
  with B_in show ?thesis 
    unfolding accepted_def by blast
qed

theorem Lang_if_accepted: 
  assumes "accepted P A w"
    shows "w \<in> Lang P A"
proof -
  from assms obtain Z where Z_nxts: "Z \<in> nxts_rlin2_set P {A} w" and Z_eps: "(Z,[]) \<in> P"
    unfolding accepted_def by blast
  from Z_nxts obtain B where B_der: "P \<turnstile> [Nt B] \<Rightarrow>* map Tm w @ [Nt Z]" and B_in: "B \<in> {A}"
    using nxts_to_mult_derive by fast
  from B_in have A_eq_B: "A = B" by simp
  from Z_eps have "P \<turnstile> [Nt Z] \<Rightarrow> []" 
    using derive_singleton[of P "Nt Z" "[]"] by simp
  hence "P \<turnstile> map Tm w @ [Nt Z] \<Rightarrow> map Tm w"
    using derive_prepend[of P "[Nt Z]" "[]" "map Tm w"] by simp
  with B_der A_eq_B have "P \<turnstile> [Nt A] \<Rightarrow>* map Tm w" by simp
  thus ?thesis 
    unfolding Lang_def by blast
qed

theorem Lang_iff_accepted_if_rlin2:
assumes "rlin2 P"
shows "w \<in> Lang P A \<longleftrightarrow> accepted P A w"
  using accepted_if_Lang[OF assms] Lang_if_accepted by fast

end