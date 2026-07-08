(*
  File:     More_Dominated_Convergence.thy
  Author:   Manuel Eberl, University of Innsbruck
*)
section \<open>Auxiliary material on filters and dominated convergence\<close>
theory More_Dominated_Convergence
  imports "HOL-Complex_Analysis.Complex_Analysis" "HOL-Library.Going_To_Filter"
begin

subsection \<open>Linear orders with unbounded sequences\<close>

text \<open>
  We define type classes for linear orders that contain sequences that ``tend to infinity''.
  These are also known as ``countably cofinite''.
\<close>
(* Move to to HOL.Filter *)

class seq_at_top = linorder +
  assumes seq_at_top_aux: "\<exists>f::nat \<Rightarrow> 'a. \<forall>x. eventually (\<lambda>n. f n \<ge> x) sequentially"

lemma seq_at_top: "\<exists>f::nat \<Rightarrow> 'a :: seq_at_top. filterlim f at_top sequentially"
  using seq_at_top_aux unfolding filterlim_at_top by blast

lemma seq_at_topI [intro?]:
  "filterlim (f :: nat \<Rightarrow> 'a :: linorder) at_top sequentially \<Longrightarrow> OFCLASS('a, seq_at_top_class)"
  by intro_classes (auto simp: filterlim_at_top)


class seq_at_bot = linorder +
  assumes seq_at_bot_aux: "\<exists>f::nat \<Rightarrow> 'a. \<forall>x. eventually (\<lambda>n. f n \<le> x) sequentially"

lemma seq_at_bot: "\<exists>f::nat \<Rightarrow> 'a :: seq_at_bot. filterlim f at_bot sequentially"
  using seq_at_bot_aux unfolding filterlim_at_bot by blast

lemma seq_at_botI [intro?]:
  "filterlim (f :: nat \<Rightarrow> 'a :: linorder) at_bot sequentially \<Longrightarrow> OFCLASS('a, seq_at_bot_class)"
  by intro_classes (auto simp: filterlim_at_bot)


text \<open>
  An archimedian field is countably cofinite, i.e.\ there exist sequences that tend to $\pm\infty$.
\<close>
(* Move to somewhere in HOL. Filter or Archimedian_Field if possible. *)
context archimedean_field
begin

lemma eventually_of_nat_ge: "eventually (\<lambda>n. of_nat n \<ge> x) sequentially"
proof -
  obtain m where "of_int m \<ge> x"
    using ex_le_of_int[of x] by blast
  hence m: "of_nat (nat m) \<ge> x"
    by (metis le_cases of_int_0_le_iff of_nat_0_le_iff of_nat_nat order.trans)
  show ?thesis
    using eventually_ge_at_top[of "nat m"]
  proof eventually_elim
    case (elim n)
    thus ?case
      using order.trans of_nat_le_iff m by blast
  qed
qed

subclass seq_at_top
proof
  show "\<exists>f. \<forall>x::'a. \<forall>\<^sub>F n in sequentially. x \<le> f n" using eventually_of_nat_ge
    by metis
qed

subclass seq_at_bot
proof
  have "eventually (\<lambda>n. -of_nat n \<le> x) sequentially" for x :: 'a
    using eventually_of_nat_ge[of "-x"] by eventually_elim (simp add: minus_le_iff)
  thus "\<exists>f. \<forall>x::'a. \<forall>\<^sub>F n in sequentially. x \<ge> f n"
    by metis
qed

end


text \<open>
  Complete linear orders are obviously countably cofinite, since even the singleton set
  \<^term>\<open>{top}\<close> is cofinite.
\<close>
(* Move to HOL.Filter *)
context complete_linorder
begin

subclass seq_at_top
proof
  show "\<exists>f. \<forall>x::'a. \<forall>\<^sub>F n in sequentially. x \<le> f n"
    by (rule exI[of _ "\<lambda>n. top_class.top"]) auto
qed

subclass seq_at_bot
proof
  show "\<exists>f. \<forall>x::'a. \<forall>\<^sub>F n in sequentially. f n \<le> x"
    by (rule exI[of _ "\<lambda>n. bot_class.bot"]) auto
qed

end



(* Move to HOL.Filter *)
instance nat :: seq_at_bot
proof
  show "filterlim (\<lambda>n::nat. 0 :: nat) at_bot sequentially"
    by (subst filterlim_at_bot) simp_all
qed

instance nat :: seq_at_top
proof
  show "filterlim (\<lambda>n. n) at_top sequentially"
    by (rule filterlim_ident)
qed

instance int :: seq_at_top
proof
  show "filterlim int at_top sequentially"
    by (metis filterlim_int_sequentially)
qed

instance int :: seq_at_bot
proof
  show "filterlim (\<lambda>n. -int n) at_bot sequentially"
    by (rule filterlim_compose[OF _ filterlim_int_sequentially])
       (simp add: at_bot_mirror eventually_filtermap filterlim_iff)
qed



subsection \<open>Countably generated filters\<close>

(* TODO: Move the whole definition of "countably generated filter" and everything related to
   countably generated filters to a more suitable place. Ideally HOL.Filter, but if that is not 
   possible because we don't have countability there we have to find another place for it) *)

text \<open>
  For convenience, we show that if we have a countably generated filter, we can assume w.l.o.g.\ 
  that the sequence of sets generating it is decreasing.
\<close>
lemma countably_generated_filterI_decseq:
  assumes "antimono_on UNIV B" "\<And>P. eventually P F \<longleftrightarrow> (\<exists>i::nat. \<forall>x\<in>B i. P x)"
  shows   "countably_generated_filter F"
  unfolding countably_generated_filter_def
proof
  show "F = (INF n. principal (B n))"
  proof (rule filter_eqI)
    fix P :: "'a \<Rightarrow> bool"
    have *: "\<exists>x. B x \<subseteq> B a \<and> B x \<subseteq> B b" for a b
      by (rule exI[of _ "max a b"]) (use monotoneD[OF assms(1)] in auto)
    show "eventually P F \<longleftrightarrow> eventually P (INF n. principal (B n))"
      by (subst eventually_INF_base) (use * assms(2) in \<open>auto simp: eventually_principal\<close>)
  qed
qed

lemma countably_generated_filter_iff_decseq:
  "countably_generated_filter F \<longleftrightarrow>
    (\<exists>B. antimono_on UNIV B \<and> (\<forall>P. eventually P F \<longleftrightarrow> (\<exists>i::nat. \<forall>x\<in>B i. P x)))"
  using countably_generated_filterI_decseq countably_generated_filter_has_antimono_basis
  by metis

lemma countably_generated_filter_altdef:
  "countably_generated_filter F \<longleftrightarrow> (\<exists>U. countable U \<and> F = (INF X\<in>U. principal X))"
proof
  assume "countably_generated_filter F"
  then obtain U where "F = (INF n::nat. principal (U n))"
    unfolding countably_generated_filter_def by blast
  thus "(\<exists>U. countable U \<and> F = (INF X\<in>U. principal X))"
    by (intro exI[of _ "range U"]) (simp_all add: image_image)
next
  assume "\<exists>U. countable U \<and> F = (INF X\<in>U. principal X)"
  then obtain U where U: "countable U" "F = (INF X\<in>U. principal X)"
    by blast
  define B where "B = from_nat_into (insert UNIV U)"
  have "(INF n. principal (B n)) = Inf ((\<lambda>X. principal X) ` range B)"
    by (simp add: image_image)
  also have "range B = insert UNIV U"
    unfolding B_def using range_from_nat_into[of "insert {} U"] U by simp
  also have "Inf (principal ` insert UNIV U) = F"
    using U by simp
  finally have *: "F = (INF n. principal (B n))"  ..
  show "countably_generated_filter F"
    unfolding countably_generated_filter_def by (rule exI, rule *)
qed

text \<open>
  Countably generated filters are sequential, i.e.\ if any sequence that tends to the filter
  is eventually contained in some set, then that set is in the filter.
\<close>
lemma countably_generated_filter_sequential:
  assumes "countably_generated_filter F"
  assumes "(\<And>f. filterlim f F sequentially \<Longrightarrow> eventually (\<lambda>n. P (f n)) sequentially)"
  shows   "eventually P F"
proof -
  obtain B where B: "antimono_on UNIV B" "\<And>P. eventually P F \<longleftrightarrow> (\<exists>i::nat. \<forall>x\<in>B i. P x)"
    using countably_generated_filter_has_antimono_basis[OF assms(1)] by metis
  have *: "\<forall>P. (\<exists>i. Ball (B i) P) \<longrightarrow> (\<exists>N. \<forall>n\<ge>N. P (f n)) \<Longrightarrow> \<exists>n::nat. P (f n)" for f
    using assms unfolding B(2) filterlim_iff eventually_at_top_linorder
    by blast
  from * show "eventually P F"
    using decseqD[OF B(1)] unfolding B(2) filterlim_iff eventually_at_top_linorder subset_iff
    by metis
qed


named_theorems countably_generated_filter_intros

lemma countably_generated_filter_top [countably_generated_filter_intros]: 
  "countably_generated_filter top_class.top"
  unfolding countably_generated_filter_altdef by (rule exI[of _ "{}"]) simp_all

lemma countably_generated_filter_bot [countably_generated_filter_intros]:
  "countably_generated_filter bot_class.bot"
  unfolding countably_generated_filter_altdef by (rule exI[of _ "{{}}"]) simp_all

lemma countably_generated_filter_principal [countably_generated_filter_intros]:
  "countably_generated_filter (principal A)"
  unfolding countably_generated_filter_altdef by (rule exI[of _ "{A}"]) simp_all

lemma countably_based_filtermap [countably_generated_filter_intros]:
  assumes "countably_generated_filter F"
  shows   "countably_generated_filter (filtermap f F)"
proof -
  obtain B where B: "antimono_on UNIV B" "\<And>P. eventually P F \<longleftrightarrow> (\<exists>i::nat. \<forall>x\<in>B i. P x)"
    using countably_generated_filter_has_antimono_basis[OF assms] by metis
  show ?thesis
  proof (rule countably_generated_filterI_decseq)
    show "antimono_on UNIV (\<lambda>i. f ` B i)"
      by (intro monotoneI image_mono monotoneD[OF B(1)])
  next
    fix P show "eventually P (filtermap f F) \<longleftrightarrow> (\<exists>i. \<forall>x\<in>f ` B i. P x)"
      unfolding eventually_filtermap B(2) by blast
  qed
qed

lemma countably_based_filtercomap [countably_generated_filter_intros]: 
  assumes "countably_generated_filter F"
  shows   "countably_generated_filter (filtercomap f F)"
proof -
  obtain B where B: "antimono_on UNIV B" "\<And>P. eventually P F \<longleftrightarrow> (\<exists>i::nat. \<forall>x\<in>B i. P x)"
    using countably_generated_filter_has_antimono_basis[OF assms] by metis
  show ?thesis
  proof (rule countably_generated_filterI_decseq)
    show "antimono_on UNIV (\<lambda>i. f -` B i)"
      by (intro monotoneI vimage_mono monotoneD[OF B(1)])
  next
    fix P show "eventually P (filtercomap f F) \<longleftrightarrow> (\<exists>i. \<forall>x\<in>f -` B i. P x)"
      unfolding eventually_filtercomap B(2) by fast
  qed
qed

lemma countably_generated_filter_inf [countably_generated_filter_intros]:
  assumes "countably_generated_filter F" "countably_generated_filter G"
  shows   "countably_generated_filter (inf F G)"
proof -
  obtain BF where BF: "antimono_on UNIV BF" "F = (INF n::nat. principal (BF n))"
    using countably_generated_filter_has_antimono_basis[OF assms(1)] by metis
  obtain BG where BG: "antimono_on UNIV BG" "G = (INF n::nat. principal (BG n))"
    using countably_generated_filter_has_antimono_basis[OF assms(2)] by metis
  have "inf F G = Inf (range (\<lambda>n. principal (BF n)) \<union> range (\<lambda>n. principal (BG n)))"
    unfolding BF BG by (rule Inf_union_distrib [symmetric])
  also have "range (\<lambda>n. principal (BF n)) \<union> range (\<lambda>n. principal (BG n)) = 
               principal ` (range BF \<union> range BG)"
    by blast
  finally have "inf F G = Inf (principal ` (range BF \<union> range BG))" .
  moreover have "countable (range BF \<union> range BG)"
    by blast
  ultimately show ?thesis 
    unfolding countably_generated_filter_altdef by blast
qed

lemma countably_generated_filter_sup [countably_generated_filter_intros]:
  assumes "countably_generated_filter F" "countably_generated_filter G"
  shows   "countably_generated_filter (sup F G)"
proof -
  obtain BF where BF: "antimono_on UNIV BF" "\<And>P. eventually P F \<longleftrightarrow> (\<exists>i::nat. \<forall>x\<in>BF i. P x)"
    using countably_generated_filter_has_antimono_basis[OF assms(1)] by metis
  obtain BG where BG: "antimono_on UNIV BG" "\<And>P. eventually P G \<longleftrightarrow> (\<exists>i::nat. \<forall>x\<in>BG i. P x)"
    using countably_generated_filter_has_antimono_basis[OF assms(2)] by metis
  show ?thesis
  proof (rule countably_generated_filterI_decseq)
    show "antimono_on UNIV (\<lambda>i. BF i \<union> BG i)"
      by (intro monotone_onI Un_mono antimonoD[OF BF(1)] antimonoD[OF BG(1)])
  next
    show "eventually P (sup F G) \<longleftrightarrow> (\<exists>i. \<forall>x\<in>BF i\<union>BG i. P x)" for P
    proof
      assume "(\<exists>i. \<forall>x\<in>BF i\<union>BG i. P x)"
      thus "eventually P (sup F G)"
        by (auto simp: eventually_sup BF BG)
    next
      assume "eventually P (sup F G)"
      then obtain i j where ij: "\<forall>x\<in>BF i. P x" "\<forall>x\<in>BG j. P x"
        by (auto simp: BF BG eventually_sup)
      define k where "k = max i j"
      have "BF k \<subseteq> BF i" "BG k \<subseteq> BG j"
        by (rule antimonoD[OF BF(1)] antimonoD[OF BG(1)]; simp add: k_def; fail)+
      thus "(\<exists>i. \<forall>x\<in>BF i\<union>BG i. P x)"
        by (intro exI[of _ k]) (use ij in auto)
    qed
  qed
qed

lemma countably_generated_filter_prod [countably_generated_filter_intros]:
  assumes "countably_generated_filter F" "countably_generated_filter G"
  shows   "countably_generated_filter (F \<times>\<^sub>F G)"
proof -
  obtain BF where BF: "countable BF" "F = Inf (principal ` BF)"
    using assms(1) unfolding countably_generated_filter_altdef by metis
  obtain BG where BG: "countable BG" "G = Inf (principal ` BG)"
    using assms(2) unfolding countably_generated_filter_altdef by metis
  define BF' where "BF' = insert UNIV BF"
  define BG' where "BG' = insert UNIV BG"
  have [simp]: "BF' \<noteq> {}" "BG' \<noteq> {}"
    by (auto simp: BF'_def BG'_def)
  define B where "B = ((\<lambda>(X,Y). X \<times> Y) ` (BF'\<times>BG'))"

  have "F \<times>\<^sub>F G = Inf (principal ` BF') \<times>\<^sub>F Inf (principal ` BG')"
    by (simp_all add: BF BG BF'_def BG'_def)
  also have "\<dots> = (INF X\<in>BF'. INF Y\<in>BG'. principal (X \<times> Y))"
    by (subst prod_filter_INF) (simp_all add: principal_prod_principal)
  also have "\<dots> = (INF (X,Y)\<in>BF'\<times>BG'. principal (X \<times> Y))"
    by (subst INF_pair) (simp add: case_prod_unfold)
  finally have "F \<times>\<^sub>F G = Inf (principal ` B)"
    by (simp add: image_image case_prod_unfold B_def)
  moreover have "countable B"
    unfolding B_def BF'_def BG'_def using BF(1) BG(1) by auto
  ultimately show ?thesis
    unfolding countably_generated_filter_altdef by blast
qed

lemma countably_generated_filter_Inf [countably_generated_filter_intros]:
  assumes "countable F" "\<And>G. G \<in> F \<Longrightarrow> countably_generated_filter G"
  shows   "countably_generated_filter (Inf F)"
proof -
  have "\<forall>G\<in>F. \<exists>B. antimono_on UNIV B \<and> G = (INF n::nat. principal (B n))"
    using countably_generated_filter_has_antimono_basis[OF assms(2)] by metis
  then obtain B where B: "\<And>G. G \<in> F \<Longrightarrow> antimono_on UNIV (B G)" 
                         "\<And>G. G \<in> F \<Longrightarrow> G = (INF n::nat. principal (B G n))"
    by metis
  define B' where "B' = (\<lambda>(G,n). B G n) ` (F \<times> UNIV)"

  have "F = (\<lambda>G. (INF n::nat. principal (B G n))) ` F"
    using B(2) by auto
  also have "Inf \<dots> = (INF p\<in>F\<times>UNIV. principal (B (fst p) (snd p)))"
    by (rule INF_pair)
  also have "\<dots> = (INF X\<in>B'. principal X)"
    by (simp add: B'_def image_image case_prod_unfold)
  finally have "Inf F = (INF X\<in>B'. principal X)" .
  moreover have "countable B'"
    unfolding B'_def using assms(1) by blast
  ultimately show ?thesis
    unfolding countably_generated_filter_altdef by blast
qed

lemma countably_generated_filter_Sup_finite [countably_generated_filter_intros]:
  assumes "finite F" "\<And>G. G \<in> F \<Longrightarrow> countably_generated_filter G"
  shows   "countably_generated_filter (Sup F)"
  using assms
  by (induction rule: finite_induct) (auto intro!: countably_generated_filter_intros)

lemma countably_generated_filter_going_to [countably_generated_filter_intros]:
  assumes "countably_generated_filter F"
  shows   "countably_generated_filter (f going_to F within A)"
  unfolding going_to_within_def by (intro countably_generated_filter_intros assms)

lemma countably_generated_filter_at_top [countably_generated_filter_intros]:
  "countably_generated_filter (at_top :: 'a :: seq_at_top filter)"
proof -
  from seq_at_top obtain f :: "nat \<Rightarrow> 'a" where f: "filterlim f at_top sequentially"
    by blast
  define B where "B = (\<lambda>n. {f n..})"
  have *: "at_top = (INF n. principal (B n))"
  proof (rule filter_eqI)
    fix P :: "'a \<Rightarrow> bool"
    have "\<exists>x. f a \<le> f x \<and> f b \<le> f x" for a b
      by (rule exI[of _ "if f a \<le> f b then b else a"]) auto
    hence "eventually P (INF n. principal (B n)) \<longleftrightarrow> (\<exists>i. \<forall>x\<in>B i. P x)"
      by (subst eventually_INF_base) (auto simp: eventually_principal B_def)
    also have "\<dots> \<longleftrightarrow> eventually P at_top"
      using f unfolding eventually_at_top_linorder filterlim_at_top B_def
      by (metis le_left_mono le_refl atLeast_iff)
    finally show "eventually P at_top \<longleftrightarrow> eventually P (INF n. principal (B n))"
      by (simp add: B_def)
  qed
  show "countably_generated_filter (at_top :: 'a filter)"
    unfolding countably_generated_filter_def by (rule exI, rule *)
qed

lemma countably_generated_filter_at_top [countably_generated_filter_intros]:
  "countably_generated_filter (at_top :: 'a :: {second_countable_topology,linorder_topology} filter)"
  oops

lemma countably_generated_filter_at_bot [countably_generated_filter_intros]:
  "countably_generated_filter (at_bot :: 'a :: seq_at_bot filter)"
proof -
  from seq_at_bot obtain f :: "nat \<Rightarrow> 'a" where f: "filterlim f at_bot sequentially"
    by blast
  define B where "B = (\<lambda>n. {..f n})"
  have *: "at_bot = (INF n. principal (B n))"
  proof (rule filter_eqI)
    fix P :: "'a \<Rightarrow> bool"
    have "\<exists>x. f a \<ge> f x \<and> f b \<ge> f x" for a b
      by (rule exI[of _ "if f a \<le> f b then a else b"]) auto
    hence "eventually P (INF n. principal (B n)) \<longleftrightarrow> (\<exists>i. \<forall>x\<in>B i. P x)"
      by (subst eventually_INF_base) (auto simp: eventually_principal B_def)
    also have "\<dots> \<longleftrightarrow> eventually P at_bot"
      using f unfolding eventually_at_bot_linorder eventually_at_top_linorder filterlim_at_bot B_def
      by (metis atMost_iff atMost_subset_iff subset_iff)
    finally show "eventually P at_bot \<longleftrightarrow> eventually P (INF n. principal (B n))"
      by (simp add: B_def)
  qed
  show "countably_generated_filter (at_bot :: 'a filter)"
    unfolding countably_generated_filter_def by (rule exI, rule *)
qed

lemma countably_generated_filter_nhds [countably_generated_filter_intros]:
  "countably_generated_filter (nhds (x :: 'a :: first_countable_topology))"
  unfolding countably_generated_filter_def using nhds_countable[of x] by metis

lemma countably_generated_filter_at_within [countably_generated_filter_intros]:
  "countably_generated_filter (at (x :: 'a :: first_countable_topology) within A)"
  unfolding at_within_def by (intro countably_generated_filter_intros)

(* TODO Move to HOL.Limits *)
lemma at_infinity_eq_filtercomap: "at_infinity = filtercomap norm at_top"
  by (rule filter_eqI) (simp_all add: eventually_filtercomap_at_top_linorder eventually_at_infinity)

lemma countably_generated_filter_at_infinity [countably_generated_filter_intros]:
  "countably_generated_filter at_infinity"
  unfolding at_infinity_eq_filtercomap by (intro countably_generated_filter_intros)

lemmas [countably_generated_filter_intros] = countably_generated_uniformity

(* TODO: almost everywhere filter of lborel, lebesgue, maybe some general result about AE filters*)



subsection \<open>Sequential filters\<close>

(* 
  Move entire section to HOL.Filter, probably. Parts that talk about more specific filters to
  HOL.Topological_Spaces.
*)

text \<open>
  We call a filter \<^emph>\<open>sequential\<close> if it can be ``approached'' by sequences in the sense that if
  a a properties holds eventually on all sequences that approach the filter, then it also holds
  eventually for the filter.

  Importantly, any countably generated filter is sequential.
\<close>

locale sequential_filter =
  fixes F :: "'a filter"
  assumes approachable: 
    "(\<And>f. filterlim f F sequentially \<Longrightarrow> eventually (\<lambda>n. P (f n)) sequentially) \<Longrightarrow> eventually P F"
begin

lemma filterlim_sequentially_imp_filterlim:
  assumes "\<And>X. filterlim X F sequentially \<Longrightarrow> filterlim (\<lambda>n. f (X n)) G sequentially"
  shows   "filterlim f G F"
  unfolding filterlim_iff
proof safe
  fix P assume P: "eventually P G"
  show "eventually (\<lambda>x. P (f x)) F"
  proof (rule approachable)
    fix X assume "filterlim X F sequentially"
    hence "filterlim (\<lambda>n. f (X n)) G sequentially"
      by (rule assms)
    thus "eventually (\<lambda>n. P (f (X n))) sequentially"
      unfolding filterlim_iff using P by blast
  qed
qed

end


lemma sequential_filtermap: 
  assumes "sequential_filter F"
  shows   "sequential_filter (filtermap (g :: 'a \<Rightarrow> 'b) F)"
proof
  interpret sequential_filter F by fact
  fix P
  assume *: "(\<And>f. filterlim f (filtermap g F) sequentially \<Longrightarrow> \<forall>\<^sub>F n in sequentially. P (f n))"
  show "eventually P (filtermap g F)"
    unfolding eventually_filtermap
  proof (rule approachable)
    fix f assume "filterlim f F sequentially"
    hence "filtermap g (filtermap f sequentially) \<le> filtermap g F"
      by (intro filtermap_mono) (auto simp: filterlim_def)
    hence "filterlim (\<lambda>n. g (f n)) (filtermap g F) sequentially"
      unfolding filterlim_def by (simp add: filtermap_filtermap)
    thus "eventually (\<lambda>n. P (g (f n))) sequentially"
      by (rule *)
  qed
qed

lemma countably_generated_filter_imp_sequential_filter:
  assumes "countably_generated_filter F"
  shows   "sequential_filter F"
  by standard (use countably_generated_filter_sequential[OF assms] in blast)


interpretation bot: sequential_filter "bot_class.bot"
  by (intro countably_generated_filter_imp_sequential_filter countably_generated_filter_intros)

interpretation top: sequential_filter "top_class.top"
  by (intro countably_generated_filter_imp_sequential_filter countably_generated_filter_intros)

interpretation principal: sequential_filter "principal A"
  by (intro countably_generated_filter_imp_sequential_filter countably_generated_filter_intros)

interpretation nhds: sequential_filter "nhds (x :: 'a :: first_countable_topology)"
  by (intro countably_generated_filter_imp_sequential_filter countably_generated_filter_intros)

interpretation at_within: sequential_filter
  "at (x :: 'a :: first_countable_topology) within A"
  by (intro countably_generated_filter_imp_sequential_filter countably_generated_filter_intros)

interpretation at_top: sequential_filter "at_top :: 'a :: seq_at_top filter"
  by (intro countably_generated_filter_imp_sequential_filter countably_generated_filter_intros)

interpretation at_bot: sequential_filter "at_bot :: 'a :: seq_at_bot filter"
  by (intro countably_generated_filter_imp_sequential_filter countably_generated_filter_intros)

interpretation at_infinity: sequential_filter at_infinity
  by (intro countably_generated_filter_imp_sequential_filter countably_generated_filter_intros)



subsection \<open>Set-wise monotone convergence\<close>

text \<open>
  We now introduce the notion of a family of sets $A(x)$ converging to another set $B$
  ``from the inside'' as $x\to F$, in the sense that eventually $A(x) \subseteq B$ as $x\to F$ and, 
  for every $y$, eventually $y\in A(x)\longleftrightarrow y\in B$ as $x\to F$.

  That is, $A(x)$ converges to $B$ pointwise from within $B$ in the discrete topology.
  Typical examples include that e.g.\ $A(x) = [l(x),r(x)]$ converges to $(a,b)$ if $l(x)\to a^+$
  and $r(x)\to b^-$, or $A(x) = [l(x),r(x)]$ converges to $\mathbb{R}$ if $l(x)\to-\infty$ and
  $r(x)\to\infty$.
\<close>

(* TODO: move to HOL.Filter, or perhaps just to where it is first needed (i.e. Lebesgue integral) *)

definition tendsto_set :: "'b measure \<Rightarrow> ('a \<Rightarrow> 'b set) \<Rightarrow> 'b set \<Rightarrow> 'a filter \<Rightarrow> bool" where
  "tendsto_set M A B F \<longleftrightarrow>
     (\<exists>C. C \<in> null_sets M \<and> (\<forall>x. x \<notin> C \<longrightarrow> eventually (\<lambda>y. x \<in> A y \<longleftrightarrow> x \<in> B) F))"

named_theorems tendsto_set_intros

lemma tendsto_set_null_sets_transfer:
  assumes "tendsto_set M f A F" "sym_diff A B \<in> null_sets M"
  shows   "tendsto_set M f B F"
proof -
  from assms(1) obtain C where C:
    "C \<in> null_sets M" "\<And>x. x \<notin> C \<Longrightarrow> \<forall>\<^sub>F y in F. (x \<in> f y) \<longleftrightarrow> (x \<in> A)"
    by (auto simp: tendsto_set_def)
  show ?thesis
    unfolding tendsto_set_def
  proof (rule exI[of _ "C \<union> sym_diff A B"], intro conjI allI impI)
    show "C \<union> sym_diff A B \<in> null_sets M"
      using C(1) assms(2) by auto
  next
    fix x assume x: "x \<notin> C \<union> sym_diff A B"
    hence "x \<notin> C"
      by auto
    show "\<forall>\<^sub>F y in F. x \<in> f y \<longleftrightarrow> x \<in> B"
      using C(2)[OF \<open>x \<notin> C\<close>] by eventually_elim (use x in auto)
  qed
qed

lemma tendsto_set_cong:
  assumes "null_sets M = null_sets N" "eventually (\<lambda>x. f x = g x) F"
          "sym_diff A B \<in> null_sets M" "F = F'"
  shows   "tendsto_set M f A F \<longleftrightarrow> tendsto_set N g B F'"
proof -
  have "tendsto_set M f A F \<longleftrightarrow> tendsto_set N g A F"
    unfolding tendsto_set_def assms(4)[symmetric]
    by (intro arg_cong[of _ _ Ex] ext conj_cong eventually_cong[OF assms(2)] all_cong)
       (simp_all add: assms(1))
  also have "\<dots> \<longleftrightarrow> tendsto_set N g B F'"
    using tendsto_set_null_sets_transfer[of N g A F' B]
          tendsto_set_null_sets_transfer[of N g B F' A] assms by (auto simp: Un_commute)
  finally show ?thesis .
qed

lemma tendsto_set_Icc_Icc [tendsto_set_intros]:
  fixes a b :: "'a :: linorder_topology"
  assumes lim: "filterlim l (nhds a) F" "filterlim r (nhds b) F"
  assumes "{a, b} \<in> null_sets M"
  shows   "tendsto_set M (\<lambda>x. {l x..r x}) {a..b} F"
  unfolding tendsto_set_def
proof (rule exI[of _ "{a, b}"], intro conjI allI impI)
  show "{a, b} \<in> null_sets M"
    by fact
next
  fix x assume x: "x \<notin> {a, b}"
  consider "x < a" | "x \<in> {a<..<b}" | "x > b"
    using x by force
  thus "\<forall>\<^sub>F y in F. (x \<in> {l y..r y}) \<longleftrightarrow> (x \<in> {a..b})"
  proof cases
    assume x: "x < a"
    have "eventually (\<lambda>y. l y \<in> {x<..}) F"
      by (rule eventually_compose_filterlim[OF eventually_nhds_in_open lim(1)]) (use x in auto)
    thus ?thesis
      by eventually_elim (use x in auto)
  next
    assume x: "x > b"
    have "eventually (\<lambda>y. r y \<in> {..<x}) F"
      by (rule eventually_compose_filterlim[OF eventually_nhds_in_open lim(2)]) (use x in auto)
    thus ?thesis
      by eventually_elim (use x in auto)
  next
    assume x: "x \<in> {a<..<b}"
    have "eventually (\<lambda>y. l y \<in> {..<x}) F"
      by (rule eventually_compose_filterlim[OF eventually_nhds_in_open lim(1)]) (use x in auto)
    moreover have "eventually (\<lambda>y. r y \<in> {x<..}) F"
      by (rule eventually_compose_filterlim[OF eventually_nhds_in_open lim(2)]) (use x in auto)
    ultimately show "\<forall>\<^sub>F y in F. (x \<in> {l y..r y}) = (x \<in> {a..b})"
      by eventually_elim (use x in auto)
  qed
qed

lemma tendsto_set_Icc_Ici [tendsto_set_intros]:
  fixes a :: "'a :: linorder_topology"
  assumes lim: "filterlim l (nhds a) F" "filterlim r at_top F"
  assumes "{a} \<in> null_sets M"
  shows   "tendsto_set M (\<lambda>x. {l x..r x}) {a..} F"
  unfolding tendsto_set_def
proof (rule exI[of _ "{a}"], intro conjI allI impI)
  show "{a} \<in> null_sets M"
    by fact
next
  fix x assume x: "x \<notin> {a}"
  consider "x < a" | "x > a"
    using x by force
  thus "\<forall>\<^sub>F y in F. (x \<in> {l y..r y}) \<longleftrightarrow> (x \<in> {a..})"
  proof cases
    assume x: "x < a"
    have "eventually (\<lambda>y. l y \<in> {x<..}) F"
      by (rule eventually_compose_filterlim[OF eventually_nhds_in_open lim(1)]) (use x in auto)
    thus ?thesis
      by eventually_elim (use x in auto)
  next
    assume x: "x > a"
    have "eventually (\<lambda>y. l y \<in> {..<x}) F"
      by (rule eventually_compose_filterlim[OF eventually_nhds_in_open lim(1)]) (use x in auto)
    moreover have "eventually (\<lambda>y. r y \<ge> x) F"
      by (rule eventually_compose_filterlim[OF eventually_ge_at_top lim(2)])
    ultimately show "\<forall>\<^sub>F y in F. (x \<in> {l y..r y}) = (x \<in> {a..})"
      by eventually_elim (use x in auto)
  qed
qed

lemma tendsto_set_Icc_Iic [tendsto_set_intros]:
  fixes b :: "'a :: linorder_topology"
  assumes lim: "filterlim l at_bot F" "filterlim r (nhds b) F"
  assumes "{b} \<in> null_sets M"
  shows   "tendsto_set M (\<lambda>x. {l x..r x}) {..b} F"
  unfolding tendsto_set_def
proof (rule exI[of _ "{b}"], intro conjI allI impI)
  show "{b} \<in> null_sets M"
    by fact
next
  fix x assume x: "x \<notin> {b}"
  consider "x < b" | "x > b"
    using x by force
  thus "\<forall>\<^sub>F y in F. (x \<in> {l y..r y}) \<longleftrightarrow> (x \<in> {..b})"
  proof cases
    assume x: "x > b"
    have "eventually (\<lambda>y. r y \<in> {..<x}) F"
      by (rule eventually_compose_filterlim[OF eventually_nhds_in_open lim(2)]) (use x in auto)
    thus ?thesis
      by eventually_elim (use x in auto)
  next
    assume x: "x < b"
    have "eventually (\<lambda>y. l y \<le> x) F"
      by (rule eventually_compose_filterlim[OF eventually_le_at_bot lim(1)])
    moreover have "eventually (\<lambda>y. r y \<in> {x<..}) F"
      by (rule eventually_compose_filterlim[OF eventually_nhds_in_open lim(2)]) (use x in auto)
    ultimately show "\<forall>\<^sub>F y in F. (x \<in> {l y..r y}) = (x \<in> {..b})"
      by eventually_elim (use x in auto)
  qed
qed

lemma tendsto_set_Icc_UNIV [tendsto_set_intros]:
  fixes l r :: "_ \<Rightarrow> 'a :: linorder_topology"
  assumes lim: "filterlim l at_bot F" "filterlim r at_top F"
  shows   "tendsto_set M (\<lambda>x. {l x..r x}) UNIV F"
  unfolding tendsto_set_def
proof (rule exI[of _ "{}"], intro conjI allI impI)
  show "{} \<in> null_sets M"
    by simp
next
  fix x
  have "eventually (\<lambda>y. l y \<le> x) F"
    by (rule eventually_compose_filterlim[OF eventually_le_at_bot lim(1)])
  moreover have "eventually (\<lambda>y. r y \<ge> x) F"
    by (rule eventually_compose_filterlim[OF eventually_ge_at_top lim(2)])
  ultimately show "\<forall>\<^sub>F y in F. (x \<in> {l y..r y}) \<longleftrightarrow> (x \<in> UNIV)"
    by eventually_elim auto
qed

lemma tendsto_set_Ici_Ici [tendsto_set_intros]:
  fixes a :: "'a :: linorder_topology"
  assumes lim: "filterlim l (nhds a) F"
  assumes "{a} \<in> null_sets M"
  shows   "tendsto_set M (\<lambda>x. {l x..}) {a..} F"
  unfolding tendsto_set_def
proof (rule exI[of _ "{a}"], intro conjI allI impI)
  show "{a} \<in> null_sets M"
    by fact
next
  fix x assume x: "x \<notin> {a}"
  consider "x < a" | "x > a"
    using x by force
  thus "\<forall>\<^sub>F y in F. (x \<in> {l y..}) \<longleftrightarrow> (x \<in> {a..})"
  proof cases
    assume x: "x < a"
    have "eventually (\<lambda>y. l y \<in> {x<..}) F"
      by (rule eventually_compose_filterlim[OF eventually_nhds_in_open lim(1)]) (use x in auto)
    thus ?thesis
      by eventually_elim (use x in auto)
  next
    assume x: "x > a"
    have "eventually (\<lambda>y. l y \<in> {..<x}) F"
      by (rule eventually_compose_filterlim[OF eventually_nhds_in_open lim(1)]) (use x in auto)
    thus "\<forall>\<^sub>F y in F. (x \<in> {l y..}) = (x \<in> {a..})"
      by eventually_elim (use x in auto)
  qed
qed

lemma tendsto_set_Iic_Iic [tendsto_set_intros]:
  fixes b :: "'a :: linorder_topology"
  assumes lim: "filterlim r (nhds b) F"
  assumes "{b} \<in> null_sets M"
  shows   "tendsto_set M (\<lambda>x. {..r x}) {..b} F"
  unfolding tendsto_set_def
proof (rule exI[of _ "{b}"], intro conjI allI impI)
  show "{b} \<in> null_sets M"
    by fact
next
  fix x assume x: "x \<notin> {b}"
  consider "x < b" | "x > b"
    using x by force
  thus "\<forall>\<^sub>F y in F. (x \<in> {..r y}) \<longleftrightarrow> (x \<in> {..b})"
  proof cases
    assume x: "x > b"
    have "eventually (\<lambda>y. r y \<in> {..<x}) F"
      by (rule eventually_compose_filterlim[OF eventually_nhds_in_open lim(1)]) (use x in auto)
    thus ?thesis
      by eventually_elim (use x in auto)
  next
    assume x: "x < b"
    have "eventually (\<lambda>y. r y \<in> {x<..}) F"
      by (rule eventually_compose_filterlim[OF eventually_nhds_in_open lim(1)]) (use x in auto)
    thus "\<forall>\<^sub>F y in F. (x \<in> {..r y}) = (x \<in> {..b})"
      by eventually_elim (use x in auto)
  qed
qed

lemma tendsto_set_Ici_UNIV [tendsto_set_intros]:
  fixes l :: "_ \<Rightarrow> 'a :: linorder_topology"
  assumes lim: "filterlim l at_bot F"
  shows   "tendsto_set M (\<lambda>x. {l x..}) UNIV F"
  unfolding tendsto_set_def
proof (rule exI[of _ "{}"], intro conjI allI impI)
  show "{} \<in> null_sets M"
    by simp
next
  fix x :: 'a
  have "eventually (\<lambda>y. l y \<le> x) F"
    by (rule eventually_compose_filterlim[OF eventually_le_at_bot lim])
  thus "\<forall>\<^sub>F y in F. (x \<in> {l y..}) = (x \<in> UNIV)"
    by eventually_elim auto
qed

lemma tendsto_set_Iic_UNIV [tendsto_set_intros]:
  fixes r :: "_ \<Rightarrow> 'a :: linorder_topology"
  assumes lim: "filterlim r at_top F"
  shows   "tendsto_set M (\<lambda>x. {..r x}) UNIV F"
  unfolding tendsto_set_def
proof (rule exI[of _ "{}"], intro conjI allI impI)
  show "{} \<in> null_sets M"
    by simp
next
  fix x :: 'a
  have "eventually (\<lambda>y. r y \<ge> x) F"
    by (rule eventually_compose_filterlim[OF eventually_ge_at_top lim])
  thus "\<forall>\<^sub>F y in F. (x \<in> {..r y}) = (x \<in> UNIV)"
    by eventually_elim auto
qed

text \<open>
  The next version of the lemma is slightly stronger in the sense that we can also show
  $\lim_{x\to a^-} \int_0^x = \int_0^a$ (i.e.\ the endpoint is also included).
\<close>
lemma (in sequential_filter) filterlim_set_lebesgue_integral_set:
  fixes f :: "real \<Rightarrow> 'b::{banach, second_countable_topology}"
  assumes integrable: "set_integrable M B f"
  assumes measurable: "set_borel_measurable M A f" "eventually (\<lambda>x. set_borel_measurable M (X x) f) F"
  assumes X: "tendsto_set M X A F" "eventually (\<lambda>x. X x \<in> sets M) F"
  assumes subset: "eventually (\<lambda>x. X x \<subseteq> B) F"
  shows   "((\<lambda>x. set_lebesgue_integral M (X x) f) \<longlongrightarrow> set_lebesgue_integral M A f) F"
proof (rule filterlim_sequentially_imp_filterlim)
  fix g assume g: "filterlim g F sequentially"
  obtain C where C: "C \<in> null_sets M" "(\<forall>x. eventually (\<lambda>y. x \<notin> C \<longrightarrow> x \<in> X y \<longleftrightarrow> x \<in> A) F)"
    using X(1) by (auto simp: tendsto_set_def)
  have "eventually (\<lambda>n. X (g n) \<in> sets M \<and> set_borel_measurable M (X (g n)) f \<and> X (g n) \<subseteq> B) sequentially"
    by (intro eventually_conj eventually_compose_filterlim[OF _ g])
       (use C X(2) measurable(2) subset in \<open>auto simp: tendsto_set_def\<close>)
  then obtain N where N:
    "\<And>n. n \<ge> N \<Longrightarrow> X (g n) \<in> sets M" "\<And>n. n \<ge> N \<Longrightarrow> set_borel_measurable M (X (g n)) f"
    "\<And>n. n \<ge> N \<Longrightarrow> X (g n) \<subseteq> B"
    unfolding eventually_at_top_linorder by blast
  have g': "filterlim (\<lambda>n. g (n + N)) F sequentially"
    by (rule filterlim_compose[OF g filterlim_add_const_nat_at_top])

  have "(\<lambda>n. set_lebesgue_integral M (X (g (n + N))) f) \<longlonglongrightarrow> set_lebesgue_integral M A f"
    unfolding set_lebesgue_integral_def
  proof (rule integral_dominated_convergence)
    show "(\<lambda>x. indicator A x *\<^sub>R f x) \<in> borel_measurable M"
      using measurable(1) by (simp add: set_borel_measurable_def)
  next
    fix n :: nat
    show "(\<lambda>x. indicator (X (g (n + N))) x *\<^sub>R f x) \<in> borel_measurable M"
      using N(2)[of "n + N"] by (simp add: set_borel_measurable_def)
  next
    show "integrable M (\<lambda>x. norm (indicator B x *\<^sub>R f x))"
      using integrable by (intro integrable_norm) (simp add: set_integrable_def)
  next
    have "AE x in M. x \<notin> C"
      by (intro AE_not_in) (use C in auto)
    thus "AE x in M. (\<lambda>n. indicat_real (X (g (n + N))) x *\<^sub>R f x) \<longlonglongrightarrow> indicat_real A x *\<^sub>R f x"
    proof eventually_elim
      case (elim x)
      have "eventually (\<lambda>n. x \<in> X (g (n + N)) \<longleftrightarrow> x \<in> A) sequentially"
        by (rule eventually_compose_filterlim[OF _ g']) 
           (use C(2) elim in \<open>auto simp: tendsto_set_def\<close>)
      hence "eventually (\<lambda>n. indicat_real (X (g (n + N))) x *\<^sub>R f x = 
                             indicat_real A x *\<^sub>R f x) sequentially"
        by eventually_elim (auto simp: indicator_def)
      thus "(\<lambda>n. indicat_real (X (g (n + N))) x *\<^sub>R f x) \<longlonglongrightarrow> indicat_real A x *\<^sub>R f x"
        by (rule tendsto_eventually)
    qed
  next
    fix n :: nat
    have "AE x in M. x \<notin> C"
      by (intro AE_not_in) (use C in auto)
    thus "AE x in M. norm (indicator (X (g (n + N))) x *\<^sub>R f x) \<le> norm (indicator B x *\<^sub>R f x)"
    proof eventually_elim
      case (elim x)
      show "norm (indicator (X (g (n + N))) x *\<^sub>R f x) \<le> norm (indicator B x *\<^sub>R f x)"
        using N[of "n + N"] elim by (auto simp: indicator_def)
    qed
  qed
  thus "(\<lambda>n. set_lebesgue_integral M (X (g n)) f) \<longlonglongrightarrow> set_lebesgue_integral M A f"
    by (rule LIMSEQ_offset)
qed

end
