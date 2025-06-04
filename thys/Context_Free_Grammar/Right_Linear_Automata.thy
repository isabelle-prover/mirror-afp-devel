(*
Authors: Kaan Taskin, Tobias Nipkow
*)

section \<open>Relating Strongly Right-Linear Grammars and Automata\<close>

theory Right_Linear_Automata
imports
  NDA_rlin2
  "Finite_Automata_HF.Finite_Automata_HF"
  HereditarilyFinite.Finitary
begin

subsection \<open>From Strongly Right-Linear Grammar to NFA\<close>

definition nfa_rlin2 :: "('n,'t)Prods \<Rightarrow> ('n::finitary) \<Rightarrow> 't nfa" where
"nfa_rlin2 P S =
  \<lparr> states = hf_of  ` ({S} \<union> Nts P),
    init = {hf_of S},
    final = hf_of ` {A \<in> Nts P. (A,[]) \<in> P},
    nxt = \<lambda>q a. hf_of ` nxt_rlin2 P (inv hf_of q) a,
    eps = Id \<rparr>"               

context
  fixes P :: "('n::finitary,'t)Prods"
  assumes "finite P"
begin

interpretation NFA_rlin2: nfa "nfa_rlin2 P S"
unfolding nfa_rlin2_def proof (standard, goal_cases)
  case 1
  then show ?case by(simp)
next
  case 2
  then show ?case by auto
next
  case (3 q x)
  then show ?case by(auto simp add: nxt_rlin2_nts)
next
  case 4
  then show ?case using \<open>finite P\<close> by (simp add: Nts_def finite_nts_syms split_def)
qed
print_theorems

lemma nfa_init_nfa_rlin2: "nfa.init (nfa_rlin2 P S) = hf_of ` {S}"
by (simp add: nfa_rlin2_def)

lemma nfa_final_nfa_rlin2: "nfa.final (nfa_rlin2 P S) = hf_of ` {A \<in> Nts P. (A,[]) \<in> P}"
by (simp add: nfa_rlin2_def)

lemma nfa_nxt_nfa_rlin2: "nfa.nxt (nfa_rlin2 P S) (hf_of A) a = hf_of ` nxt_rlin2 P A a"
by (simp add: nfa_rlin2_def inj)

lemma nfa_epsclo_nfa_rlin2: "M \<subseteq> {hf_of S} \<union> hf_of ` Nts P \<Longrightarrow> nfa.epsclo (nfa_rlin2 P S) M = M"
unfolding NFA_rlin2.epsclo_def unfolding nfa_rlin2_def by(auto)

lemma nfa_nextl_nfa_rlin2: "M \<subseteq> {S} \<union> Nts P
  \<Longrightarrow> nfa.nextl (nfa_rlin2 P S) (hf_of ` M) xs = hf_of ` nxts_rlin2_set P M xs"
proof(induction xs arbitrary: M)
  case Nil
  then show ?case
    by (simp add: nxts_rlin2_set_def)(fastforce intro!: nfa_epsclo_nfa_rlin2)
next
  case (Cons a xs)
  let ?epsclo = "nfa.epsclo (nfa_rlin2 P S)"
  let ?nxt = "nfa.nxt (nfa_rlin2 P S)"
  let ?nxts = "nfa.nextl (nfa_rlin2 P S)"
  have "?nxts (hf_of ` M) (a # xs) = ?nxts (\<Union>x\<in>?epsclo (hf_of ` M). ?nxt x a) xs"
    by simp
  also have "\<dots> = ?nxts (\<Union>x\<in>hf_of ` M. ?nxt x a) xs"
    using Cons.prems by(subst nfa_epsclo_nfa_rlin2) auto
  also have "\<dots> = ?nxts (\<Union>m\<in>M. ?nxt (hf_of m) a) xs" by simp
  also have "\<dots> = ?nxts (\<Union>m\<in>M. hf_of ` nxt_rlin2 P m a) xs"
    by (simp add: nfa_nxt_nfa_rlin2)
  also have "\<dots> = ?nxts (hf_of ` (\<Union>m\<in>M. nxt_rlin2 P m a)) xs"
    by (metis image_UN)
  also have "\<dots> = hf_of ` nxts_rlin2_set P (\<Union>m\<in>M. nxt_rlin2 P m a) xs"
    using Cons.prems by(subst Cons.IH)(auto simp add: nxt_rlin2_nts)
  also have "\<dots> = hf_of ` nxts_rlin2_set P M (a # xs)"
    by (simp add: nxt_rlin2_set_def nxts_rlin2_set_def)
  finally show ?case .
qed

lemma lang_pres_nfa_rlin2: assumes "rlin2 P"
shows "nfa.language (nfa_rlin2 P S) = Lang P S"
proof -
  have 1: "\<And>A xs. \<lbrakk> A \<in> nxts_rlin2_set P {S} xs; A \<in> Nts P; (A, []) \<in> P\<rbrakk> \<Longrightarrow>
    P \<turnstile> [Nt S] \<Rightarrow>* map Tm xs"
    using nxts_to_mult_derive by (metis (no_types, opaque_lifting) append.right_neutral derive.intros
      r_into_rtranclp rtranclp_trans singletonD)
  have "\<And>A B. Nt B \<notin> Syms P \<Longrightarrow> (A, []) \<in> P \<Longrightarrow> A \<noteq> B" by(auto simp: Syms_def)
  hence 2: "\<And>xs. rlin2 P \<Longrightarrow> P \<turnstile> [Nt S] \<Rightarrow>* map Tm xs \<Longrightarrow>
          nxts_rlin2_set P {S} xs \<inter> {A \<in> Nts P. (A, []) \<in> P} \<noteq> {}"
   using in_Nts_iff_in_Syms mult_derive_to_nxts rlin2_tms_eps
   by (metis (no_types, lifting) Int_Collect empty_iff singletonI)
  show ?thesis
    unfolding NFA_rlin2.language_def Lang_def nfa_init_nfa_rlin2 nfa_final_nfa_rlin2
      nfa_nextl_nfa_rlin2[OF Un_upper1]
    using 2[OF assms] by (auto simp: 1)
qed

lemma regular_if_rlin2: assumes "rlin2 P"
  shows "regular (Lang P S)"
using lang_pres_nfa_rlin2[OF assms] NFA_rlin2.imp_regular[of S]
by metis

end


subsection \<open>From DFA to Strongly Right-Linear Grammar\<close>

context dfa
begin

text
\<open>We define \<open>Prods_dfa\<close> that collects the production set from the deterministic finite automata \<open>M\<close>\<close>

definition Prods_dfa :: "(hf, 'a) Prods" where
"Prods_dfa =
  (\<Union>q \<in> dfa.states M. \<Union>x. {(q,[Tm x, Nt(dfa.nxt M q x)])}) \<union> (\<Union>q \<in> dfa.final M. {(q,[])})"

lemma rlin2_prods_dfa: "rlin2 (Prods_dfa)"
  unfolding rlin2_def Prods_dfa_def by blast

text
\<open>We show that a word can be derived from the production set \<open>Prods_dfa\<close> if and only if traversing the word in the deterministic finite 
 automata \<open>M\<close> ends in a final state. The proofs are very similar to those in \<open>DFA_rlin2.thy\<close>\<close>

lemma mult_derive_to_nxtl:
  "Prods_dfa \<turnstile> [Nt A] \<Rightarrow>* map Tm w @ [Nt B] \<Longrightarrow> nextl A w = B"
proof (induction w arbitrary: B rule: rev_induct)
  case Nil
  thus ?case
    using rlin2_nts_derive_eq[OF rlin2_prods_dfa, of A B] by simp
next
  case (snoc x xs)
  from snoc.prems have "Prods_dfa \<turnstile> [Nt A] \<Rightarrow>* map Tm xs @ [Tm x,Nt B]" by simp
  then obtain C where C_der: "Prods_dfa \<turnstile> [Nt A] \<Rightarrow>* map Tm xs @ [Nt C]"
               and C_prods: "(C,[Tm x, Nt B]) \<in> Prods_dfa" using rlin2_introduce_tm[OF rlin2_prods_dfa, of A xs x B] by auto 
  have 1: "nextl A xs = C"
    using snoc.IH[OF C_der] .
  from C_prods have 2: "B = dfa.nxt M C x"
    unfolding Prods_dfa_def by blast
  from 1 2 show ?case by simp
qed

lemma nxtl_to_mult_derive:
  assumes "A \<in> dfa.states M"
    shows "Prods_dfa \<turnstile> [Nt A] \<Rightarrow>* map Tm w @ [Nt (nextl A w)]"
proof (induction w rule: rev_induct)
  case (snoc x xs)
  let ?B = "nextl A xs"
  have "?B \<in> dfa.states M" 
    using nextl_state[OF assms, of xs] .
  hence "(?B, [Tm x, Nt (dfa.nxt M ?B x)]) \<in> Prods_dfa"
    unfolding Prods_dfa_def by blast
  hence "Prods_dfa \<turnstile> [Nt ?B] \<Rightarrow> [Tm x] @ [Nt (dfa.nxt M ?B x)]"
    by (simp add: derive_singleton)
  hence "Prods_dfa \<turnstile> [Nt A] \<Rightarrow>* map Tm xs @ ([Tm x] @ [Nt (dfa.nxt M ?B x)])"
    using snoc.IH by (meson derive_prepend rtranclp.simps)
  thus ?case by auto
qed simp

theorem Prods_dfa_iff_dfa:
  "q \<in> dfa.states M \<Longrightarrow> Prods_dfa \<turnstile> [Nt q] \<Rightarrow>* map Tm w \<longleftrightarrow> nextl q w \<in> dfa.final M"
proof
  show "Prods_dfa \<turnstile> [Nt q] \<Rightarrow>* map Tm w \<Longrightarrow> nextl q w \<in> dfa.final M"
  proof -
    assume asm: "Prods_dfa \<turnstile> [Nt q] \<Rightarrow>* map Tm w"
    obtain B where q_der: "Prods_dfa \<turnstile> [Nt q] \<Rightarrow>* map Tm w @ [Nt B]" and B_in: "(B,[]) \<in> Prods_dfa" 
      unfolding Lang_def using rlin2_tms_eps[OF rlin2_prods_dfa asm] by auto
    have 1: "nextl q w = B"
      using mult_derive_to_nxtl[OF q_der] .
    from B_in have 2: "B \<in> dfa.final M"
      unfolding Prods_dfa_def by blast
    from 1 2 show ?thesis by simp
  qed
next
  assume asm1: "q \<in> dfa.states M"
  show "nextl q w \<in> dfa.final M \<Longrightarrow> Prods_dfa \<turnstile> [Nt q] \<Rightarrow>* map Tm w"
  proof -
    assume asm2: "nextl q w \<in> dfa.final M"
    let ?Z = "nextl q w"
    from asm2 have Z_eps: "(?Z,[]) \<in> Prods_dfa"
      unfolding Prods_dfa_def by blast
    have "Prods_dfa \<turnstile> [Nt q] \<Rightarrow>* map Tm w @ [Nt ?Z]"
      using nxtl_to_mult_derive[OF asm1, of w] .
    with Z_eps show ?thesis
      by (metis derives_rule rtranclp.rtrancl_refl self_append_conv)
  qed
qed

corollary dfa_language_eq_Lang: "dfa.language M = Lang Prods_dfa (dfa.init M)"
unfolding language_def Lang_def by (simp add: Prods_dfa_iff_dfa)

end

corollary rlin2_if_regular:
  "regular L \<Longrightarrow> \<exists>P S::hf. rlin2 P \<and> L = Lang P S"
by (metis dfa.dfa_language_eq_Lang dfa.rlin2_prods_dfa regular_def)

end