theory Simple_Tabulation_Hashing
imports
  Universal_Hash_Families.Universal_Hash_Families_More_Product_PMF
  Dependent_Product
  Xor_Inst
  Vec_Extras
begin

unbundle Xor.xor_syntax
unbundle Fixed_Length_Vector.vec_syntax
unbundle no Finite_Cartesian_Product.vec_syntax (* imported from HOL-Analysis *)
hide_type Finite_Cartesian_Product.vec

subsection \<open>Intro rules, contrapositives and bijections\<close>
lemma (in prob_space) k_wise_indep_varsI:
  assumes "\<And>a J. \<lbrakk> J \<subseteq> I; card J \<le> k; finite J \<rbrakk> \<Longrightarrow>
     prob {\<omega>. \<forall>i\<in>J. X i \<omega> = a i} = (\<Prod>i\<in>J. prob {\<omega>. X i \<omega> = a i})"
          "M = measure_pmf p"
  shows "k_wise_indep_vars k (\<lambda>_. count_space UNIV) X I"
  apply (simp only: k_wise_indep_vars_def prob_space_axioms)
  apply (clarsimp, rule indep_vars_pmf, rule assms(2))
  by (metis (no_types, lifting) assms(1) card_mono order_trans_rules(23))

(* used for the proof of non-4-independence *)
lemma (in prob_space) indep_vars_pmf_contrapos:
  assumes "prob {\<omega>. \<forall>x\<in>J. P x (X' x \<omega>)} \<noteq> (\<Prod>x\<in>J. prob {\<omega>. P x (X' x \<omega>)})"
          "finite J" "M = measure_pmf p"
  shows "\<not> indep_vars (\<lambda>_. count_space UNIV) X' J"
  apply (rule contrapos_nn[OF assms(1)])
  using assms by (intro split_indep_events; force)

locale (*tag:important*) bij_betw_funcsetE begin

text \<open>These lemmas prove bijections between sets of 2-arity functions and their decompositions

For example, a function $f: [0,100] \rightharpoonup \{A,B,C\} \rightharpoonup \{True,False\}$ can be decomposed into 3 parts:

$\begin{gathered}
[0,100]\rightharpoonup\{A,B,C\}\rightharpoonup\{True,False\} \ \\
\rightleftharpoons [1,100]\rightharpoonup\{A,B,C\}\rightharpoonup\{True,False\} \times \\
\{A,C\}\rightharpoonup\{True,False\} \times \\
\{True,False\} \
\end{gathered}$

\begin{itemize}
  \item base: $[1,100] \rightharpoonup \{A,B,C\} \rightharpoonup \{True,False\}$ (split the 0-index, leaving 1-100 intact)
  \item $z_0$: $\{A,C\} \rightharpoonup \{True,False\}$ (represents the 0-index, but further split the B-index)
  \item $z_b$: $B \in \{True,False\}$ (decides the value for $f\ 0\ B$)
\end{itemize}

$f$ is equivalent to its reconstruction, $f = \mathop{base}(0 := z_0(B := z_b))$\<close>

context
  fixes \<alpha> and A B :: "_ set"
  assumes \<alpha>_in_A: "\<alpha> \<in> A"
begin

lemma bij_PiE_remove_point:
  "bij_betw (\<lambda> (f, v). f(\<alpha> := v)) ((A - {\<alpha>} \<rightarrow>\<^sub>E B) \<times> B) (A \<rightarrow>\<^sub>E B)"
proof (intro bij_betw_imageI inj_onI, goal_cases "inj" "surj")
  case (inj _ _)
  then show ?case
    apply (simp add: case_prod_beta' image_iff prod_eq_iff set_eq_iff mem_Times_iff fun_eq_iff)
    by (metis Diff_iff PiE_arb insertCI)
next
  case surj
  then show ?case
  proof (intro equalityI subsetI)
    fix h assume "h \<in> A \<rightarrow>\<^sub>E B"
    with \<alpha>_in_A have "h \<alpha> \<in> B" "h(\<alpha> := undefined) \<in> A - {\<alpha>} \<rightarrow>\<^sub>E B"
      by (auto simp: PiE_def extensional_def)
    then show "h \<in> (\<lambda> (f, v). f(\<alpha> := v)) ` ((A - {\<alpha>} \<rightarrow>\<^sub>E B) \<times> B)"
      apply (simp add: case_prod_beta' image_iff)
      by (metis fun_upd_upd fun_upd_triv)
  next
    fix h assume "h \<in> (\<lambda>(f, v). f(\<alpha> := v)) ` ((A - {\<alpha>} \<rightarrow>\<^sub>E B) \<times> B)"
    with \<alpha>_in_A show "h \<in> A \<rightarrow>\<^sub>E B"
      apply (simp add: case_prod_beta' image_iff)
      by (metis insert_Diff PiE_fun_upd)
  qed
qed

text \<open>
  Helper: "Absorb" a point into a function space bijection.
  This allows chaining: if we have a bijection $F$ for a smaller domain $S \rightarrow (A-\{x\}\rightarrow B)$,
  we can automatically get a bijection for $S\ x\ B \rightarrow (A\rightarrow B)$.
\<close>
lemma bij_absorb_point:
  assumes "bij_betw F S (A - {\<alpha>} \<rightarrow>\<^sub>E B)"
  shows "bij_betw (\<lambda> (s, v). (F s)(\<alpha> := v)) (S \<times> B) (A \<rightarrow>\<^sub>E B)"
proof -
  \<comment> \<open>1. Combine $F$ with Identity on $B$\<close>
  from assms have "bij_betw (map_prod F id) (S \<times> B) ((A - {\<alpha>} \<rightarrow>\<^sub>E B) \<times> B)"
    by (blast intro: bij_betw_map_prod)
  \<comment> \<open>2. Apply the base removal lemma\<close>
  with bij_PiE_remove_point show ?thesis
    by (auto
      elim: bij_betw_trans[simplified comp_def, elim_format]
      simp: map_prod_def case_prod_beta')
qed

text \<open>
  Helper 2: "Lift Value"
  Attaches a computed value $V$ to the function at point $x$.
  Used for the outer function (e.g., @{term "a(\<alpha> := V)"}).
\<close>
lemma bij_lift_value:
  assumes "bij_betw V S B"
  shows "bij_betw (\<lambda>(f, s). f(\<alpha> := V s)) ((A - {\<alpha>} \<rightarrow>\<^sub>E B) \<times> S) (A \<rightarrow>\<^sub>E B)"
proof -
  have "bij_betw (map_prod id V) ((A - {\<alpha>} \<rightarrow>\<^sub>E B) \<times> S) ((A - {\<alpha>} \<rightarrow>\<^sub>E B) \<times> B)"
    using assms by (simp add: bij_betw_map_prod)
  with bij_PiE_remove_point show ?thesis
    by (auto
      elim: bij_betw_trans[simplified comp_def, elim_format]
      simp: map_prod_def case_prod_beta')
qed

end

text \<open>Tuple Association Helper: $((A, B), C) \longleftrightarrow (A, B, C)$\<close>
lemma bij_assoc_right_to_left:
  "bij_betw (\<lambda> (a, b, c). ((a, b), c)) (A \<times> B \<times> C) ((A \<times> B) \<times> C)"
  by (auto intro: bij_betwI[where g="\<lambda> ((a, b), c). (a, b, c)"])

lemma bij_assoc_left_to_right:
  "bij_betw (\<lambda>((a, b), c). (a, b, c)) ((A \<times> B) \<times> C) (A \<times> B \<times> C)"
  by (auto intro: bij_betwI[where g="\<lambda>(a, b, c). ((a, b), c)"])

lemma bij_betw_combine_right:
  assumes "bij_betw f B C"
  shows "bij_betw (\<lambda>(a, b). (a, f b)) (A \<times> B) (A \<times> C)"
  using assms by (simp flip: map_prod_def id_def add: case_prod_beta' bij_betw_map_prod)

subsubsection \<open>Application\<close>

lemma remove1_remove1:
  assumes "\<alpha> \<in> A" "\<beta> \<in> B" "finite A" "finite B" "finite C" "C \<noteq> {}"
  shows "bij_betw
      (\<lambda>(a,b,c). a(\<alpha> := b(\<beta> := c)))
      ((A - {\<alpha>} \<rightarrow>\<^sub>E B \<rightarrow>\<^sub>E C) \<times> (B - {\<beta>} \<rightarrow>\<^sub>E C) \<times> C)
      (A \<rightarrow>\<^sub>E B \<rightarrow>\<^sub>E C)"
proof -
  \<comment> \<open>1. Establish bijection for the value: @{term "b(\<beta> := c)"}\<close>
  have bij_val: "bij_betw (\<lambda>(b, c). b(\<beta> := c)) ((B - {\<beta>} \<rightarrow>\<^sub>E C) \<times> C) (B \<rightarrow>\<^sub>E C)"
    using bij_PiE_remove_point[OF `\<beta> \<in> B`] by auto

  \<comment> \<open>2. Lift this value to $A$\<close>
  have bij_lift: "bij_betw (\<lambda>(a, (b,c)). a(\<alpha> := b(\<beta> := c)))
                  ((A - {\<alpha>} \<rightarrow>\<^sub>E B \<rightarrow>\<^sub>E C) \<times> ((B - {\<beta>} \<rightarrow>\<^sub>E C) \<times> C))
                  (A \<rightarrow>\<^sub>E B \<rightarrow>\<^sub>E C)"
    using bij_lift_value[OF `\<alpha> \<in> A` bij_val] by (auto simp: case_prod_beta')

  \<comment> \<open>3. Fix tuple associativity $(a,b,c) \rightarrow (a,(b,c))$\<close>
  have bij_assoc: "bij_betw (\<lambda>(a,b,c). (a,(b,c)))
                   ((A - {\<alpha>} \<rightarrow>\<^sub>E B \<rightarrow>\<^sub>E C) \<times> (B - {\<beta>} \<rightarrow>\<^sub>E C) \<times> C)
                   ((A - {\<alpha>} \<rightarrow>\<^sub>E B \<rightarrow>\<^sub>E C) \<times> ((B - {\<beta>} \<rightarrow>\<^sub>E C) \<times> C))"
    by (simp add: bij_betwI[where g="\<lambda>(a, (b, c)). (a, b, c)"])

  show ?thesis
    using bij_betw_trans[OF bij_assoc bij_lift] by (simp add: case_prod_beta)
qed

lemma remove1_remove2:
  assumes "\<beta>1 \<noteq> \<beta>2" "\<alpha> \<in> A" "\<beta>1 \<in> B" "\<beta>2 \<in> B"
          "finite A" "finite B" "finite C" "C \<noteq> {}"
  shows "bij_betw
      (\<lambda>(a,b,c,d). a(\<alpha> := b(\<beta>1 := c, \<beta>2 := d)))
      ((A - {\<alpha>} \<rightarrow>\<^sub>E B \<rightarrow>\<^sub>E C) \<times> (B - {\<beta>1,\<beta>2} \<rightarrow>\<^sub>E C) \<times> C \<times> C)
      (A \<rightarrow>\<^sub>E B \<rightarrow>\<^sub>E C)"
proof -
  let ?S_B = "(B - {\<beta>1,\<beta>2} \<rightarrow>\<^sub>E C) \<times> C \<times> C"

  \<comment> \<open>1. Build bijection for value: @{term "b(\<beta>1 := c, \<beta>2 := d)"}\<close>
  \<comment> \<open>We use @{thm [source] bij_absorb_point} recursively\<close>

  have "\<beta>1 \<in> B - {\<beta>2}" using assms by simp
  \<comment> \<open>Start with remove\_point for @{term "\<beta>1"}\<close>
  have bij_B_start: "bij_betw (\<lambda>(b, c). b(\<beta>1 := c))
                     ((B - {\<beta>1,\<beta>2} \<rightarrow>\<^sub>E C) \<times> C) (B - {\<beta>2} \<rightarrow>\<^sub>E C)"
    using bij_PiE_remove_point[OF `\<beta>1 \<in> B - {\<beta>2}`] by (metis Diff_insert)

  \<comment> \<open>Absorb @{term "\<beta>2"}\<close>
  have bij_B_next: "bij_betw (\<lambda>((b, c), d). b(\<beta>1 := c, \<beta>2 := d))
                    (((B - {\<beta>1,\<beta>2} \<rightarrow>\<^sub>E C) \<times> C) \<times> C) (B \<rightarrow>\<^sub>E C)"
    using bij_absorb_point[OF `\<beta>2 \<in> B` bij_B_start] by (simp add: case_prod_beta')

  \<comment> \<open>Flatten tuple for $B$\<close>
  have bij_B_val: "bij_betw (\<lambda>(b,c,d). b(\<beta>1 := c, \<beta>2 := d)) ?S_B (B \<rightarrow>\<^sub>E C)"
    using bij_betw_trans[OF bij_assoc_right_to_left bij_B_next]
    by (simp add: case_prod_beta' comp_def)

  \<comment> \<open>2. Lift to $A$\<close>
  have bij_lift: "bij_betw (\<lambda>(a, (b,c,d)). a(\<alpha> := b(\<beta>1 := c, \<beta>2 := d)))
                  ((A - {\<alpha>} \<rightarrow>\<^sub>E B \<rightarrow>\<^sub>E C) \<times> ?S_B) (A \<rightarrow>\<^sub>E B \<rightarrow>\<^sub>E C)"
    using bij_lift_value[OF `\<alpha> \<in> A` bij_B_val] by (simp add: case_prod_beta' comp_def)

  \<comment> \<open>3. Fix tuple associativity\<close>
  have bij_assoc: "bij_betw (\<lambda>(a,b,c,d). (a,(b,c,d)))
                   ((A - {\<alpha>} \<rightarrow>\<^sub>E B \<rightarrow>\<^sub>E C) \<times> ?S_B)
                   ((A - {\<alpha>} \<rightarrow>\<^sub>E B \<rightarrow>\<^sub>E C) \<times> ?S_B)"
    by (simp add: bij_betwI [where g="\<lambda>(a, (b,c,d)). (a,b,c,d)"])

  show ?thesis
    using bij_betw_trans[OF bij_assoc bij_lift]  by (simp add: case_prod_beta)
qed

lemma remove1_remove3:
  assumes "\<beta>1 \<noteq> \<beta>2" "\<beta>2 \<noteq> \<beta>3" "\<beta>3 \<noteq> \<beta>1" "\<alpha> \<in> A" "\<beta>1 \<in> B" "\<beta>2 \<in> B" "\<beta>3 \<in> B"
          "finite A" "finite B" "finite C" "C \<noteq> {}"
  shows "bij_betw
      (\<lambda>(a,b,c,d,e). a(\<alpha> := b(\<beta>1 := c, \<beta>2 := d, \<beta>3 := e)))
      ((A - {\<alpha>} \<rightarrow>\<^sub>E B \<rightarrow>\<^sub>E C) \<times> (B - {\<beta>1,\<beta>2,\<beta>3} \<rightarrow>\<^sub>E C) \<times> C \<times> C \<times> C)
      (A \<rightarrow>\<^sub>E B \<rightarrow>\<^sub>E C)"
proof -
  let ?DomB3 = "B - {\<beta>1,\<beta>2,\<beta>3} \<rightarrow>\<^sub>E C"
  let ?S_B = "?DomB3 \<times> C \<times> C \<times> C"

  \<comment> \<open>1. Build bijection for value $B$ recursively\<close>

  \<comment> \<open>Step 1: Base @{term "\<beta>1"}\<close>
  from assms bij_PiE_remove_point[of "\<beta>1" "B - {\<beta>3, \<beta>2}"]
  have "bij_betw (\<lambda>(b,c). b(\<beta>1:=c)) (?DomB3 \<times> C) (B - {\<beta>3, \<beta>2} \<rightarrow>\<^sub>E C)"
    by (auto simp flip: Diff_insert simp: insert_commute)

  \<comment> \<open>Step 2: Absorb @{term "\<beta>2"}\<close>
  with assms bij_absorb_point[of "\<beta>2" "B - {\<beta>3}"]
  have "bij_betw (\<lambda>((b,c),d). b(\<beta>1:=c, \<beta>2:=d)) ((?DomB3 \<times> C) \<times> C) (B - {\<beta>3} \<rightarrow>\<^sub>E C)"
    by (auto simp flip: Diff_insert simp: case_prod_beta' insert_commute)

  \<comment> \<open>Step 3: Absorb @{term "\<beta>3"}\<close>
  with assms bij_absorb_point[of "\<beta>3" B]
  have bij_3: "bij_betw (\<lambda>(((b,c),d),e). b(\<beta>1:=c, \<beta>2:=d, \<beta>3:=e)) (((?DomB3 \<times> C) \<times> C) \<times> C) (B \<rightarrow>\<^sub>E C)"
    by (auto simp: case_prod_beta' insert_commute)

  moreover have "bij_betw (\<lambda>(b,c,d,e). (((b,c),d),e)) ?S_B (((?DomB3 \<times> C) \<times> C) \<times> C)"
    by (auto intro: bij_betwI[where g="\<lambda>(((b,c),d),e). (b,c,d,e)"])

  \<comment> \<open>Step 4: Flatten tuple for $B$\<close>
  ultimately have "bij_betw (\<lambda>(b,c,d,e). b(\<beta>1:=c, \<beta>2:=d, \<beta>3:=e)) ?S_B (B \<rightarrow>\<^sub>E C)"
    by (auto
      elim: bij_betw_trans[simplified comp_def, elim_format]
      simp: case_prod_beta')

  \<comment> \<open>2. Lift to $A$\<close>
  with bij_lift_value assms
  have bij_lift: "bij_betw (\<lambda>(a, (b,c,d,e)). a(\<alpha> := b(\<beta>1:=c, \<beta>2:=d, \<beta>3:=e)))
                  ((A - {\<alpha>} \<rightarrow>\<^sub>E B \<rightarrow>\<^sub>E C) \<times> ?S_B) (A \<rightarrow>\<^sub>E B \<rightarrow>\<^sub>E C)"
    by (simp add: case_prod_beta')

  \<comment> \<open>3. Fix tuple associativity\<close>
  have bij_assoc: "bij_betw (\<lambda>(a,b,c,d,e). (a,(b,c,d,e)))
                   ((A - {\<alpha>} \<rightarrow>\<^sub>E B \<rightarrow>\<^sub>E C) \<times> ?S_B)
                   ((A - {\<alpha>} \<rightarrow>\<^sub>E B \<rightarrow>\<^sub>E C) \<times> ?S_B)"
    by (auto intro: bij_betwI [where g="\<lambda>(a, (b,c,d,e)). (a,b,c,d,e)"])

  with bij_betw_trans[OF bij_assoc bij_lift] show ?thesis
    by (simp add: case_prod_beta)
qed

lemma remove2_remove2'remove1:
  assumes "\<alpha>1 \<noteq> \<alpha>2" "\<beta>1 \<noteq> \<beta>2" "\<alpha>1 \<in> A" "\<alpha>2 \<in> A" "\<beta>1 \<in> B" "\<beta>2 \<in> B" "\<beta>3 \<in> B"
          "finite A" "finite B" "finite C" "C \<noteq> {}"
  shows "bij_betw
      (\<lambda>(a,b,c,d,e,f). a(\<alpha>1 := b(\<beta>1 := d, \<beta>2 := e), \<alpha>2 := c(\<beta>3 := f)))
      ((A - {\<alpha>1, \<alpha>2} \<rightarrow>\<^sub>E B \<rightarrow>\<^sub>E C) \<times> (B - {\<beta>1, \<beta>2} \<rightarrow>\<^sub>E C) \<times> (B - {\<beta>3} \<rightarrow>\<^sub>E C) \<times> C \<times> C \<times> C)
      (A \<rightarrow>\<^sub>E B \<rightarrow>\<^sub>E C)"
proof -
  let ?DomA = "A - {\<alpha>1, \<alpha>2} \<rightarrow>\<^sub>E B \<rightarrow>\<^sub>E C"
  let ?DomB1 = "B - {\<beta>1, \<beta>2} \<rightarrow>\<^sub>E C"
  let ?DomB2 = "B - {\<beta>3} \<rightarrow>\<^sub>E C"

  have "bij_betw (\<lambda>(b,d,e). ((b,d),e)) (?DomB1 \<times> C \<times> C) ((?DomB1 \<times> C) \<times> C)"
    by (auto intro: bij_betwI[where g="\<lambda>((b,d),e). (b,d,e)"])

  moreover from assms bij_absorb_point[of "\<beta>2" "B"] bij_PiE_remove_point[of "\<beta>1" "B - {\<beta>2}"]
  have "bij_betw (\<lambda>((b,d),e). b(\<beta>1:=d, \<beta>2:=e)) ((?DomB1 \<times> C) \<times> C) (B \<rightarrow>\<^sub>E C)"
    by (auto simp flip: Diff_insert simp: case_prod_beta')

  \<comment> \<open>1. Val 1: @{term "b(\<beta>1 := d, \<beta>2 := e)"}\<close>
  ultimately have "bij_betw (\<lambda>(b, d, e). b(\<beta>1 := d, \<beta>2 := e)) (?DomB1 \<times> C \<times> C) (B \<rightarrow>\<^sub>E C)"
    by (auto elim: bij_betw_trans[simplified comp_def, elim_format] simp: case_prod_beta')

  \<comment> \<open>2. Val 2: @{term "c(\<beta>3 := f)"}\<close>
  moreover from bij_PiE_remove_point[of "\<beta>3" B] assms
  have "bij_betw (\<lambda>(c, f). c(\<beta>3 := f)) (?DomB2 \<times> C) (B \<rightarrow>\<^sub>E C)" by auto

  \<comment> \<open>3. Combine values (Product Step)\<close>
  \<comment> \<open>We explicitly form the tuple structure $((B1,C,C), (B2,C))$\<close>
  ultimately have bij_vals: "bij_betw
      (\<lambda>((b,d,e), (c,f)). (b(\<beta>1:=d, \<beta>2:=e), c(\<beta>3:=f)))
      ((?DomB1 \<times> C \<times> C) \<times> (?DomB2 \<times> C))
      ((B \<rightarrow>\<^sub>E C) \<times> (B \<rightarrow>\<^sub>E C))"
    by (fastforce dest: bij_betw_map_prod simp add: map_prod_def id_def case_prod_beta')

  \<comment> \<open>4. Lift to Parallel\<close>
  from bij_betw_map_prod[OF bij_betw_id bij_vals] have bij_parallel:
    "bij_betw
      (\<lambda>(a, rest). (a, (\<lambda>((b,d,e), (c,f)). (b(\<beta>1:=d, \<beta>2:=e), c(\<beta>3:=f))) rest))
      (?DomA \<times> ((?DomB1 \<times> C \<times> C) \<times> (?DomB2 \<times> C)))
      (?DomA \<times> ((B \<rightarrow>\<^sub>E C) \<times> (B \<rightarrow>\<^sub>E C)))"
    by (auto simp: map_prod_def id_def case_prod_beta')

  have bij_A_step1: "bij_betw (\<lambda>((a, v1), v2). (a(\<alpha>1 := v1), v2))
                 ((?DomA \<times> (B \<rightarrow>\<^sub>E C)) \<times> (B \<rightarrow>\<^sub>E C)) ((A - {\<alpha>2} \<rightarrow>\<^sub>E B \<rightarrow>\<^sub>E C) \<times> (B \<rightarrow>\<^sub>E C))"
    using assms bij_lift_value[of "\<alpha>1" "A - {\<alpha>2}"]
    by (force
      intro: bij_betw_map_prod simp flip: map_prod_def id_def Diff_insert
      simp: case_prod_beta')

  have bij_A_step2: "bij_betw (\<lambda>(a, v2). a(\<alpha>2 := v2))
                 ((A - {\<alpha>2} \<rightarrow>\<^sub>E B \<rightarrow>\<^sub>E C) \<times> (B \<rightarrow>\<^sub>E C)) (A \<rightarrow>\<^sub>E B \<rightarrow>\<^sub>E C)"
    using assms bij_PiE_remove_point[of "\<alpha>2" "A"] by (auto simp: case_prod_beta')

  \<comment> \<open>5. Explicit Shuffle\<close>
  have bij_shuffle: "bij_betw (\<lambda>(a, b, c, d, e, f). (a, (b, d, e), (c, f)))
      (?DomA \<times> ?DomB1 \<times> ?DomB2 \<times> C \<times> C \<times> C)
      (?DomA \<times> (?DomB1 \<times> C \<times> C) \<times> (?DomB2 \<times> C))"
    by (auto intro: bij_betwI[where g="\<lambda>(a, (b, d, e), (c, f)). (a, b, c, d, e, f)"])

  \<comment> \<open>6. Final Chain - broken into steps to avoid unification issues\<close>
  have "bij_betw (\<lambda>(a, (b,d,e), (c,f)). ((a, b(\<beta>1:=d, \<beta>2:=e)), c(\<beta>3:=f)))
        (?DomA \<times> (?DomB1 \<times> C \<times> C) \<times> (?DomB2 \<times> C))
        ((?DomA \<times> (B \<rightarrow>\<^sub>E C)) \<times> (B \<rightarrow>\<^sub>E C))"
  proof -
    have "bij_betw (\<lambda>(a, v1, v2). ((a, v1), v2))
          (?DomA \<times> (B \<rightarrow>\<^sub>E C) \<times> (B \<rightarrow>\<^sub>E C)) ((?DomA \<times> (B \<rightarrow>\<^sub>E C)) \<times> (B \<rightarrow>\<^sub>E C))"
      by (rule bij_betwI [where g="\<lambda>((a,v1),v2). (a,v1,v2)"]) auto
    with bij_parallel show ?thesis
      by (auto elim: bij_betw_trans[simplified comp_def, elim_format] simp: case_prod_beta')
  qed

  with bij_shuffle have
    "bij_betw (\<lambda>(a, b, c, d, e, f). ((a, b(\<beta>1:=d, \<beta>2:=e)), c(\<beta>3:=f)))
      (?DomA \<times> ?DomB1 \<times> ?DomB2 \<times> C \<times> C \<times> C)
      ((?DomA \<times> (B \<rightarrow>\<^sub>E C)) \<times> (B \<rightarrow>\<^sub>E C))"
    by (auto elim: bij_betw_trans[simplified comp_def, elim_format] simp: case_prod_beta')

  moreover from bij_A_step1 bij_A_step2 have
    "bij_betw (\<lambda>((a, v1), v2). a(\<alpha>1 := v1, \<alpha>2 := v2))
      ((?DomA \<times> (B \<rightarrow>\<^sub>E C)) \<times> (B \<rightarrow>\<^sub>E C))
      (A \<rightarrow>\<^sub>E B \<rightarrow>\<^sub>E C)"
    by (auto elim: bij_betw_trans[simplified comp_def, elim_format] simp: case_prod_beta')

  ultimately show ?thesis
    by (auto elim: bij_betw_trans[simplified comp_def, elim_format] simp: case_prod_beta')
qed

end (* locale bij_prod *)

section \<open>Definitions\<close>

locale simple_tabulation_hashing =
  fixes n :: "'n :: {index1, zero} itself" \<comment> \<open>key length, i.e. 4 for 4 'fragments\<close>
  fixes r :: "'result :: {abel_group_xor, finite} itself" \<comment> \<open>bool or any type that supports xor\<close>
  fixes q :: "'q :: index1 itself" \<comment> \<open>digest length, i.e. 3\<close>
  fixes d :: "'fragment :: finite itself" \<comment> \<open>domain of input key fragments\<close>
  assumes n: "n = TYPE('n)"
begin

text \<open>
In tabulation hashing, keys are split into \emph{n} fragments, each piece hashed individually,
before being combined into a final digest with the XOR operator.
  i.e. $x \equiv [x_0,x_1,x_2]$, $h(x) \equiv h_0 x_0 \oplus h_1 x_1 \oplus h_2 x_2$

Therefore, the type variable 'n, CARD('n) and n must reflect the number of parts in a key. In the
example above, 'n = 3 (which is an alias for num1 bit1)

The final digest length is indicated by the type variable 'q, and 'result is any type that supports
xor. For example, 'result = bool. When using 'result = bool and 'q = 3, it can be interpreted as
using a 3-bit word as the output, which can encode $2^3=8$ possibilities, e.g. [True, False, True]\<close>

abbreviation cardn :: "'n itself \<Rightarrow> nat" where "cardn _ \<equiv> CARD('n)"

abbreviation N :: "'n itself \<Rightarrow> nat set" where "N type \<equiv> {..<cardn type}"

abbreviation D :: "'fragment set" where "D \<equiv> UNIV"

abbreviation Dn :: "('fragment, 'n) vec set" (\<open>D\<^sup>n\<close>) where
  \<comment> \<open>domain of all possible input keys s.t. each key is composed of exactly *n* fragments\<close>
  "D\<^sup>n \<equiv> UNIV"

abbreviation R :: "('result, 'q) vec set" where
  \<comment> \<open>range of all possible outputs, s.t. each output is composed of exactly *q* bits\<close>
  "R \<equiv> UNIV"

abbreviation H :: "'n itself \<Rightarrow> (nat \<Rightarrow> 'fragment \<Rightarrow> ('result, 'q) vec) set" where
  \<comment> \<open>set of all possible assignments and combinations for every column-item pair\<close>
  "H type \<equiv> N type \<rightarrow>\<^sub>E D \<rightarrow>\<^sub>E R"

definition tb_S :: "'n itself \<Rightarrow> (nat \<Rightarrow> 'fragment \<Rightarrow> ('result, 'q) vec) pmf" where
  \<comment> \<open>Generator of instances of H\<close>
  "tb_S _ \<equiv> pmf_of_set (H n)"

definition tb_H :: "('fragment, 'n) vec \<Rightarrow> (nat \<Rightarrow> 'fragment \<Rightarrow> ('result, 'q) vec) \<Rightarrow> ('result, 'q) vec" where
  \<comment> \<open>Applies the tabulation hashing algorithm on *k* using a hash function from H\<close>
  "tb_H k h \<equiv> xor_fold (map (\<lambda>i. h i (k $ to_index i)) ([0..<cardn n]))"

lemma tb_S_alt_def:
  shows "tb_S n = prod_pmf (N n) (\<lambda>_. prod_pmf UNIV (\<lambda>_. pmf_of_set R))"
  unfolding tb_S_def
  by (simp add: Pi_pmf_of_set PiE_defaut_undefined_eq)

lemma tb_H_absorb:
  assumes "i < CARD('n)"
  shows "tb_H x h \<oplus> c = tb_H x (h(i := (h i)(x $ to_index i := h i (x $ to_index i) \<oplus> c)))"
  unfolding tb_H_def
  by (auto intro!: arg_cong[where f = xor_fold] simp: fold_absorb[of i] assms)

lemma tb_H_absorb':
  shows "tb_H x h \<oplus> c =
    tb_H x (h(from_index i := (h (from_index i))(x $ i := h (from_index i) (x $ i) \<oplus> c)))"
  by (metis from_index_bound from_to_index tb_H_absorb)

lemma tb_H_extract:
  assumes "i < CARD('n)"
  shows "tb_H x (h(i := g(x $ to_index i := \<alpha>))) = tb_H x (h(i := g(x $ to_index i := 0))) \<oplus> \<alpha>"
  by (subst tb_H_absorb[OF assms]) simp

lemma tb_H_extract':
  shows "tb_H x (h(from_index i := g(x $ i := \<alpha>))) = tb_H x (h(from_index i := g(x $ i := 0))) \<oplus> \<alpha>"
  by (metis from_index_bound from_to_index tb_H_extract)

lemma tb_H_exch:
  assumes "i < CARD('n)"
  shows "tb_H x (a(i := aa(x $ to_index i := b))) = \<alpha> \<longleftrightarrow>
     b = tb_H x (a(i := aa(x $ to_index i := \<alpha>)))"
  apply (subst (1 2) tb_H_extract[OF assms])
  by (metis (no_types, lifting) assoc abel_group_xor_class.eq_iff)

lemma (*tag:important*) tb_H_exch':
  shows "tb_H x (a(from_index i := aa(x $ i := b))) = \<alpha> \<longleftrightarrow>
     b = tb_H x (a(from_index i := aa(x $ i := \<alpha>)))"
  by (metis from_index_bound from_to_index tb_H_exch)

lemma (*tag:important*) tb_H_discard:
  assumes "x $ i \<noteq> y $ i"
  shows "tb_H x (a(from_index i := b(y $ i := c))) = tb_H x (a(from_index i := b))"
  unfolding tb_H_def
  apply (intro arg_cong[where ?f = "xor_fold"])
  by (simp_all add: assms)

section \<open>Proofs\<close>

subsection \<open>Proof of 1-independence and uniformity\<close>

lemma (*tag:important*) prob_tb_H_bin:
  shows "measure_pmf.prob (tb_S n) {h. tb_H x h = \<alpha>} = 1 / real (card R)" (is "?lhs = ?rhs")
proof -
  let ?N = "N n"
  let ?H = "H n"
  let ?tb_S = "tb_S n"
  let ?x0 = "x $ to_index 0"

  note finite_PiE[simp] PiE_eq_empty_iff[simp] measure_pmf_single[simp]

  have bij:
    "bij_betw (\<lambda>(a, b, c). a(0 := b(?x0 := c)))
      ((?N - {0} \<rightarrow>\<^sub>E D \<rightarrow>\<^sub>E R) \<times> (D - {?x0} \<rightarrow>\<^sub>E R) \<times> R)
      ?H"
    by (fastforce intro!: bij_betw_funcsetE.remove1_remove1)

  let ?destructure =
    "pair_pmf (pmf_of_set (?N - {0} \<rightarrow>\<^sub>E D \<rightarrow>\<^sub>E R))
      (pair_pmf (pmf_of_set (D - {?x0} \<rightarrow>\<^sub>E R))
        (pmf_of_set R))"

  have asmap: "?tb_S =
     map_pmf (\<lambda>(a, b, c). a(0 := b(?x0 := c))) ?destructure"
    unfolding tb_S_def
    by (simp add: bij flip: pmf_of_set_prod_eq map_pmf_of_set_bij_betw del: PiE_UNIV)

  have "?lhs =
    measure_pmf.prob ?destructure
      (Sigma UNIV (\<lambda>h.
        Sigma UNIV (\<lambda>Z.
          {tb_H x (h(0 := Z(?x0 := \<alpha>)))})))"
    unfolding asmap measure_map_pmf by (clarsimp intro!: measure_pmf_cong tb_H_exch)

  also have "\<dots> = ?rhs" by (simp add: measure_pmf_prob_dependent_product_bound_eq')

  finally show ?thesis .
qed

theorem uniform:
  shows "prob_space.uniform_on (tb_S n) (tb_H key) R"
  using prob_tb_H_bin by (auto intro!: measure_pmf.uniform_onI)

subsection \<open>Proof of two-independence\<close>

lemma prob_tb_H_bin1_bin2:
  assumes "x \<noteq> y"
  shows "measure_pmf.prob (tb_S n) {h. tb_H x h = \<alpha> \<and> tb_H y h = \<beta>} = 1 / real (card R * card R)"
  (is "?lhs = ?rhs")
proof -
  let ?N = "N n"
  let ?H = "H n"
  let ?tb_S = "tb_S n"

  note finite_PiE[simp] PiE_eq_empty_iff[simp] measure_pmf_single[simp]

  obtain i where i: "x $ i \<noteq> y $ i" by (meson assms vec_cong)

  let ?xi = "x $ i"
  let ?yi = "y $ i"

  have bij:
    "bij_betw (\<lambda>(a, b, c, d). a(from_index i := b(?xi := c, ?yi := d)))
      ((?N - {from_index i} \<rightarrow>\<^sub>E D \<rightarrow>\<^sub>E R) \<times> (D - {?xi, ?yi} \<rightarrow>\<^sub>E R) \<times> R \<times> R)
      ?H"
    using i by (intro bij_betw_funcsetE.remove1_remove2) simp_all

  let ?destructure =
    "pair_pmf (pmf_of_set (?N - {from_index i} \<rightarrow>\<^sub>E D \<rightarrow>\<^sub>E R))
      (pair_pmf (pmf_of_set (D - {?xi, ?yi} \<rightarrow>\<^sub>E R))
        (pmf_of_set (R \<times> R)))"

  have asmap: "?tb_S =
     map_pmf (\<lambda>(a, b, c, d). a(from_index i := b(?xi := c, ?yi := d))) ?destructure"
    unfolding tb_S_def
    by (simp add: bij flip: pmf_of_set_prod_eq map_pmf_of_set_bij_betw
        del: PiE_UNIV UNIV_Times_UNIV)

  have "?lhs =
    measure_pmf.prob ?destructure
      (Sigma UNIV (\<lambda>h.
        Sigma UNIV (\<lambda>I.
          {(xi',yi'). tb_H x (h(from_index i := I(?xi := xi', ?yi := yi'))) = \<alpha> \<and>
                      tb_H y (h(from_index i := I(?xi := xi', ?yi := yi'))) = \<beta> })))"
    unfolding asmap measure_map_pmf by (auto intro: measure_pmf_cong)

  also from i have "\<dots> =
    measure_pmf.prob ?destructure
      (Sigma UNIV (\<lambda>h.
        Sigma UNIV (\<lambda>I.
          {(tb_H x (h(from_index i := I(?xi := \<alpha>, ?yi := \<beta>))),
            tb_H y (h(from_index i := I(?xi := \<alpha>, ?yi := \<beta>))))})))"
    apply (clarsimp intro!: measure_pmf_cong simp: tb_H_discard tb_H_exch')
    by (smt (verit, ccfv_threshold) fun_upd_twist tb_H_discard)

  also have "\<dots> = ?rhs" by (simp add: measure_pmf_prob_dependent_product_bound_eq')

  finally show ?thesis .
qed

subsection \<open>Proof of 3-independence\<close>

lemma prob_3same_conv:
  assumes "x $ i \<noteq> y $ i" "y $ i \<noteq> z $ i" "z $ i \<noteq> x $ i"
  shows "measure_pmf.prob (tb_S n) {h. tb_H x h = \<alpha> \<and> tb_H y h = \<beta> \<and> tb_H z h = \<gamma>} =
    1 / (real (card R) * real (card R) * real (card R))" (is "?lhs = ?rhs")
proof -
  let ?N = "N n"
  let ?H = "H n"
  let ?tb_S = "tb_S n"
  let ?xi = "x $ i"
  let ?yi = "y $ i"
  let ?zi = "z $ i"

  note finite_PiE[simp] PiE_eq_empty_iff[simp] measure_pmf_single[simp]

  from assms have bij:
    "bij_betw (\<lambda>(a, b, c, d, e). a(from_index i := b(?xi := c, ?yi := d, ?zi := e)))
      ((?N - {from_index i} \<rightarrow>\<^sub>E D \<rightarrow>\<^sub>E R) \<times> (D - {?xi, ?yi, ?zi} \<rightarrow>\<^sub>E R) \<times> R \<times> R \<times> R)
      ?H"
    by (fastforce intro: bij_betw_funcsetE.remove1_remove3)

  let ?destructure =
    "(pair_pmf (pmf_of_set (?N - {from_index i} \<rightarrow>\<^sub>E D \<rightarrow>\<^sub>E R))
       (pair_pmf (pmf_of_set (D - {?xi, ?yi, ?zi} \<rightarrow>\<^sub>E R))
         (pmf_of_set (R \<times> R \<times> R))))"

  have asmap: "?tb_S =
     map_pmf (\<lambda>(a, b, c, d, e). a(from_index i := b(?xi := c, ?yi := d, ?zi := e))) ?destructure"
    unfolding tb_S_def
    by (simp add: bij flip: pmf_of_set_prod_eq map_pmf_of_set_bij_betw
        del: PiE_UNIV UNIV_Times_UNIV)

  have "?lhs =
    measure_pmf.prob ?destructure
      (Sigma UNIV (\<lambda>h.
          Sigma UNIV (\<lambda>I.
            {(xi',yi',zi').
              tb_H x (h(from_index i := I(?xi := xi', ?yi := yi', ?zi := zi'))) = \<alpha> \<and>
              tb_H y (h(from_index i := I(?xi := xi', ?yi := yi', ?zi := zi'))) = \<beta> \<and>
              tb_H z (h(from_index i := I(?xi := xi', ?yi := yi', ?zi := zi'))) = \<gamma>})))"
    unfolding asmap measure_map_pmf by (auto intro: measure_pmf_cong)

  also from assms have "\<dots> =
    measure_pmf.prob ?destructure
      (Sigma UNIV (\<lambda>h.
          Sigma UNIV (\<lambda>I.
            {(xi',yi',zi').
              tb_H x (h(from_index i := I(?xi := xi'))) = \<alpha> \<and>
              tb_H y (h(from_index i := I(?yi := yi'))) = \<beta> \<and>
              tb_H z (h(from_index i := I(?zi := zi'))) = \<gamma>})))"
    unfolding asmap measure_map_pmf
    apply (clarsimp intro!: measure_pmf_cong simp: tb_H_discard)
    by (smt (verit, best) fun_upd_twist tb_H_discard)

  also have "\<dots> =
    (measure_pmf.prob ?destructure
      (Sigma UNIV (\<lambda>h.
        Sigma UNIV (\<lambda>I.
          {let xi' = tb_H x (h(from_index i := I(?xi := \<alpha>)));
               yi' = tb_H y (h(from_index i := I(?yi := \<beta>)));
               zi' = tb_H z (h(from_index i := I(?zi := \<gamma>)))
           in (xi',yi',zi')}))))"
    by (auto simp add: tb_H_exch' intro: measure_pmf_cong conj_cong)

  also have "\<dots> = ?rhs" by (simp add: measure_pmf_prob_dependent_product_bound_eq')

  finally show ?thesis .
qed

lemma prob_2same_conv:
  assumes "x $ i \<noteq> y $ i" "z $ j \<noteq> x $ j" "i \<noteq> j"
      and "z $ i = x $ i"
  shows "measure_pmf.prob (tb_S n) {h. tb_H x h = \<alpha> \<and> tb_H y h = \<beta> \<and> tb_H z h = \<gamma>} =
    1 / (real (card R) * real (card R) * real (card R))" (is "?lhs = ?rhs")
proof -
  let ?N = "N n"
  let ?H = "H n"
  let ?tb_S = "tb_S n"

  let ?xi = "x $ i"
  let ?yi = "y $ i"
  let ?zi = "z $ i"
  let ?xj = "x $ j"
  let ?yj = "y $ j"
  let ?zj = "z $ j"

  note finite_PiE[simp] PiE_eq_empty_iff[simp] measure_pmf_single[simp]

  from assms have bij:
    "bij_betw
      (\<lambda>(a, b, c, d, e, f). a(from_index i := b(?xi := d, ?yi := e), from_index j := c(?zj := f)))
      ((?N - {from_index i, from_index j} \<rightarrow>\<^sub>E D \<rightarrow>\<^sub>E R) \<times>
        (D - {?xi, ?yi} \<rightarrow>\<^sub>E R) \<times>
        (D - {?zj} \<rightarrow>\<^sub>E R) \<times>
        R \<times> R \<times> R)
      ?H"
    by (fastforce intro: bij_betw_funcsetE.remove2_remove2'remove1)

  let ?destructure = "
    (pair_pmf (pmf_of_set (?N - {from_index i, from_index j} \<rightarrow>\<^sub>E D \<rightarrow>\<^sub>E R))
      (pair_pmf (pmf_of_set (D - {?xi, ?yi} \<rightarrow>\<^sub>E R))
        (pair_pmf (pmf_of_set (D - {?zj} \<rightarrow>\<^sub>E R))
          (pmf_of_set (R \<times> R \<times> R)))))"

  have asmap: "?tb_S =
    map_pmf
      (\<lambda>(a, b, c, d, e, f). a(from_index i := b(?xi := d, ?yi := e), from_index j := c(?zj := f)))
      ?destructure"
    unfolding tb_S_def
    by (simp add: bij flip: pmf_of_set_prod_eq map_pmf_of_set_bij_betw
        del: PiE_UNIV UNIV_Times_UNIV)

  have "?lhs =
    (measure_pmf.prob ?destructure
      (Sigma UNIV (\<lambda>h.
        Sigma UNIV (\<lambda>I.
          Sigma UNIV (\<lambda>J.
            {(xi',yi',zj').
   tb_H x (h(from_index i := I(?xi := xi', ?yi := yi'), from_index j := J(?zj := zj'))) = \<alpha> \<and>
   tb_H y (h(from_index i := I(?xi := xi', ?yi := yi'), from_index j := J(?zj := zj'))) = \<beta> \<and>
   tb_H z (h(from_index i := I(?xi := xi', ?yi := yi'), from_index j := J(?zj := zj'))) = \<gamma>
            })))))"
    unfolding asmap measure_map_pmf by (auto intro: measure_pmf_cong)

   also from assms have "\<dots> =
    (measure_pmf.prob ?destructure
      (Sigma UNIV (\<lambda>h.
        Sigma UNIV (\<lambda>I.
          Sigma UNIV (\<lambda>J.
            {(xi',yi',zj').
   tb_H x (h(from_index j := J, from_index i := I(?xi := xi'))) = \<alpha> \<and>
   tb_H y (h(from_index j := J(?zj := zj'), from_index i := I(?yi := yi'))) = \<beta> \<and>
   tb_H z (h(from_index i := I(?xi := xi'), from_index j := J(?zj := zj'))) = \<gamma>
            })))))"
    unfolding asmap measure_map_pmf
    apply (clarsimp intro!: measure_pmf_cong dest!: from_index_neq simp: tb_H_discard)
    by (smt (verit, best) fun_upd_twist tb_H_discard)

  also have "\<dots> =
    measure_pmf.prob ?destructure
      (Sigma UNIV (\<lambda>h.
        Sigma UNIV (\<lambda>I.
          Sigma UNIV (\<lambda>J.
            {let
    xi' = tb_H x (h(from_index j := J, from_index i := I(?xi := \<alpha>)));
    zj' = tb_H z (h(from_index i := I(?xi := xi'), from_index j := J(?zj := \<gamma>)));
    yi' = tb_H y (h(from_index j := J(?zj := zj'), from_index i := I(?yi := \<beta>)))
            in (xi',yi',zj')}))))"
    by (auto simp add: Let_unfold tb_H_exch' intro: measure_pmf_cong)

  also have "\<dots> = ?rhs" by (simp add: measure_pmf_prob_dependent_product_bound_eq')

  finally show ?thesis .
qed

lemma prob_tb_H_bin1_bin2_bin3:
  assumes "x \<noteq> y" "y \<noteq> z" "z \<noteq> x"
  shows "measure_pmf.prob (tb_S n) {h. tb_H x h = \<alpha> \<and> tb_H y h = \<beta> \<and> tb_H z h = \<gamma>} =
    1 / (real (card R) * real (card R) * real (card R))" (is "?lhs = ?rhs")
proof -
  obtain i where i: "x $ i \<noteq> y $ i" using assms(1) vec_cong by blast

  let ?xi = "x $ i"
  let ?yi = "y $ i"
  let ?zi = "z $ i"

  consider "?zi \<noteq> ?xi \<and> ?zi \<noteq> ?yi" | "?zi = ?xi" | "?zi = ?yi" by blast
  then show ?thesis
  proof cases
    case 2
    moreover from assms vec_cong obtain j where "z $ j \<noteq> x $ j" by blast
    ultimately show ?thesis using i assms by (auto intro: prob_2same_conv)
  next
    case 3
    moreover obtain j where "z $ j \<noteq> y $ j" using assms(2) vec_cong by blast
    ultimately show ?thesis
      using i assms
      by (subst prob_2same_conv[where y = x, symmetric]) (auto simp: ac_simps)
  qed (auto intro!: prob_3same_conv simp: assms i)
qed

subsection \<open>Proof of 3-universal\<close>

lemma three_indep_vars:
  shows "prob_space.k_wise_indep_vars (tb_S n) 3 (\<lambda>_. count_space R) tb_H D\<^sup>n"
proof (rule prob_space.k_wise_indep_varsI)
  show "prob_space (measure_pmf (tb_S n))" using measure_pmf.prob_space_axioms by blast
  show "measure_pmf (tb_S n) = measure_pmf (tb_S n)" by (rule refl)
next
  fix J :: "('fragment, 'n) vec set" assume "card J \<le> 3" "finite J" (* a k-subset of D\<^sup>n *)
  fix f
  consider (0) "card J = 0"
         | (1) "card J = 1"
         | (2) "card J = 2"
         | (3) "card J = 3" using \<open>card J \<le> 3\<close> by linarith
  then show "measure_pmf.prob (tb_S n) {h. \<forall>key\<in>J. tb_H key h = f key} =
    (\<Prod>key\<in>J. measure_pmf.prob (tb_S n) {h. tb_H key h = f key})"
    (is "?lhs = ?rhs")
  proof cases
    case 0
    then have "J = {}" using \<open>finite J\<close> card_0_eq by blast
    then have "?lhs = 1" by simp
    also have  "\<dots> = ?rhs" unfolding \<open>J = {}\<close> prod.empty ..
    finally show ?thesis .
  next
    case 1
    then have "\<exists>key. J = {key}" by (meson card_1_singletonE)
    then obtain key where [simp]: "J = {key}" by blast
    \<comment> \<open>Since there is only one value inhabiting J, we can erase the quantifier\<close>
    then have "?lhs = measure_pmf.prob (tb_S n) {h. tb_H key h = f key}" by simp
    also have "\<dots> = ?rhs" by simp
    finally show ?thesis .
  next
    case 2
    then have "\<exists>k1 k2. J = {k1,k2} \<and> k1 \<noteq> k2" by (meson card_2_iff)
    then obtain k1 k2 where [simp]: "J = {k1,k2}" "k1 \<noteq> k2" by blast+

    have "?lhs = measure_pmf.prob (tb_S n) {h. tb_H k1 h = f k1 \<and> tb_H k2 h = f k2}" by simp
    also have "\<dots> = 1 / (real (card R) * real (card R))" using prob_tb_H_bin1_bin2 by simp
    also have "\<dots> = (\<Prod>key\<in>J. indicat_real R (f key) / real (card R))" by simp
    also have "\<dots> = ?rhs" using prob_tb_H_bin by fastforce
    finally show ?thesis .
  next
    case 3
    then have "\<exists>k1 k2 k3. J = {k1,k2,k3} \<and> k1 \<noteq> k2 \<and> k2 \<noteq> k3 \<and> k3 \<noteq> k1" by (metis card_3_iff)
    then obtain k1 k2 k3 where [simp]: "J = {k1,k2,k3}" "k1 \<noteq> k2" "k2 \<noteq> k3" "k3 \<noteq> k1" "k1 \<noteq> k3"
       by blast+

    have "?lhs = measure_pmf.prob (tb_S n)
      {h. tb_H k1 h = f k1 \<and> tb_H k2 h = f k2 \<and> tb_H k3 h = f k3}" by simp
    also have "\<dots> = 1 / (real (card R) * real (card R) * real (card R))"
      using prob_tb_H_bin1_bin2_bin3 by simp
    also have "\<dots> = (\<Prod>key\<in>J. indicat_real R (f key) / real (card R))" by simp
    also have "\<dots> = ?rhs" using prob_tb_H_bin by fastforce
    finally show ?thesis .
  qed
qed

theorem three_universal:
  shows "prob_space.k_universal (tb_S n) 3 tb_H D\<^sup>n R"
  using prob_space.k_universal_def measure_pmf.prob_space_axioms three_indep_vars uniform by blast

subsection \<open>Proof of non-4-universal\<close>

lemma prob_4_conv:
  fixes u v :: 'fragment
  assumes "W \<oplus> X \<oplus> Y \<oplus> Z = 0" "\<And>h. P (h(0 := undefined, Suc 0 := undefined)) = P h"
          "CARD('n) > Suc 0" "u \<noteq> v"
  shows "measure_pmf.prob (tb_S n) {h::nat \<Rightarrow> 'fragment \<Rightarrow> ('result, 'q) vec.
     h 0 u \<oplus> h (Suc 0) u \<oplus> P h = W \<and>
     h 0 u \<oplus> h (Suc 0) v \<oplus> P h = X \<and>
     h 0 v \<oplus> h (Suc 0) u \<oplus> P h = Y \<and>
     h 0 v \<oplus> h (Suc 0) v \<oplus> P h = Z }
    = 1 / (real (card R) * real (card R) * real (card R))" (is "?lhs = ?rhs")
proof -
  let ?N = "N n"
  let ?H = "H n"
  let ?tb_S = "tb_S n"

  note assms(1,2) [simp]
  note finite_PiE[simp] PiE_eq_empty_iff[simp] measure_pmf_single[simp]

  define W' X' Y' Z' where
    "W' \<equiv> \<lambda>h. W \<oplus> P h"
    "X' \<equiv> \<lambda>h. X \<oplus> P h"
    "Y' \<equiv> \<lambda>h. Y \<oplus> P h"
    "Z' \<equiv> \<lambda>h. Z \<oplus> P h"

  have xor_sum:  "W' h \<oplus> X' h \<oplus> Y' h \<oplus> Z' h = 0" for h
    by (simp add: W'_X'_Y'_Z'_def commute left_commute)

  have bij:
    "bij_betw
      (\<lambda>(a, b, c, d, e, f). a(Suc 0 := b(u := d, v := e), 0 := c(v := f)))
      ((?N - {Suc 0, 0} \<rightarrow>\<^sub>E D \<rightarrow>\<^sub>E R) \<times>
        (D - {u, v} \<rightarrow>\<^sub>E R) \<times>
        (D - {v} \<rightarrow>\<^sub>E R) \<times>
        R \<times> R \<times> R)
      ?H"
    using assms by (intro bij_betw_funcsetE.remove2_remove2'remove1) simp_all

  let ?destructure =
    "(pair_pmf (pmf_of_set (?N - {Suc 0, 0} \<rightarrow>\<^sub>E D \<rightarrow>\<^sub>E R))
      (pair_pmf (pmf_of_set (D - {u, v} \<rightarrow>\<^sub>E R))
        (pair_pmf (pmf_of_set (D - {v} \<rightarrow>\<^sub>E R))
          (pmf_of_set (R \<times> R \<times> R)))))"

  have asmap: "?tb_S =
    map_pmf
      (\<lambda>(a, b, c, d, e, f). a(1 := b(u := d, v := e), 0 := c(v := f)))
      ?destructure"
    unfolding tb_S_def
    by (simp add: bij flip: pmf_of_set_prod_eq map_pmf_of_set_bij_betw
        del: PiE_UNIV UNIV_Times_UNIV)

  have "?lhs =
    (measure_pmf.prob ?destructure
      (Sigma UNIV (\<lambda>h.
        Sigma UNIV (\<lambda>I1.
          Sigma UNIV (\<lambda>I0.
            {(u1,v1,v0).
              I0 u \<oplus> u1 \<oplus> P h = W \<and>
              I0 u \<oplus> v1 \<oplus> P h = X \<and>
              v0   \<oplus> u1 \<oplus> P h = Y \<and>
              v0   \<oplus> v1 \<oplus> P h = Z})))))"
    unfolding asmap measure_map_pmf
    apply (clarsimp intro!: measure_pmf_cong simp add: assms(4))
    by (smt (z3) array_rules(5) assms(2) fun_upd_twist)

  (* note: it helps the solver when we group \<open>W \<oplus> P h\<close> into \<open>W' h\<close> *)
  also have "\<dots> =
    measure_pmf.prob ?destructure
      (Sigma UNIV (\<lambda>h.
        Sigma UNIV (\<lambda>I1.
          Sigma UNIV (\<lambda>I0.
            {(u1,v1,v0).
              I0 u \<oplus> u1 = W' h \<and>
              I0 u \<oplus> v1 = X' h \<and>
              v0   \<oplus> u1 = Y' h \<and>
              v0   \<oplus> v1 = Z' h }))))"
    apply (clarsimp intro!: measure_pmf_cong)
    unfolding W'_X'_Y'_Z'_def
    by (smt (verit, best) assoc right_neutral self_inv)

  also have "\<dots> =
    measure_pmf.prob ?destructure
      (Sigma UNIV (\<lambda>h.
        Sigma UNIV (\<lambda>I1.
          Sigma UNIV (\<lambda>I0.
            {(I0 u \<oplus> W' h,
              I0 u \<oplus> X' h,
              I0 u \<oplus> W' h \<oplus> Y' h)}))))"
    apply (clarsimp intro!: measure_pmf_cong)
    by (smt (z3) xor_sum assoc abel_group_xor_class.eq_iff)

  also have "\<dots> = ?rhs"
    apply (subst measure_pmf_prob_dependent_product_bound_eq'[where r = "?rhs"])+
    by simp_all

  finally show ?thesis .
qed

lemma not_four_indep:
  assumes "CARD('n) > 1" \<comment> \<open>if n = 1, then tabulation hashing is 4-independent\<close>
          "card D \<ge> 2" \<comment> \<open>if D = {} or D = {x}, then it is impossible to obtain 4 distinct keys\<close>
          "card R > 1" \<comment> \<open>tabulation hashing is 4-independent otherwise\<close>
  shows "\<not> prob_space.k_wise_indep_vars (tb_S n) 4 (\<lambda>_. count_space R) tb_H D\<^sup>n"
proof -
  let ?tb_S = "tb_S n"
  fix f :: "('fragment, 'n) vec \<Rightarrow> ('result, 'q) vec"

  obtain u v :: "'fragment" where pq [simp]: "u \<noteq> v" by (meson assms(2) UNIV_I card_2_iff' ex_card)
  define u_n where "u_n \<equiv> replicate (CARD('n) - 2) u"

  let ?w = "u # u # u_n"
  let ?x = "u # v # u_n"
  let ?y = "v # u # u_n"
  let ?z = "v # v # u_n"

  define w x y z :: "('fragment, 'n) vec" where wxyz:
    "w = vec_of_list ?w" "x = vec_of_list ?x" "y = vec_of_list ?y" "z = vec_of_list ?z"
  define J where [simp]: "J = {w,x,y,z}"

  (* Preliminaries start *)
  have N: "a # b # u_n \<in> {xs. length xs = CARD('n)}" for a b
    unfolding u_n_def using assms(1) by simp

  have distinct [simp]: "w \<noteq> x" "w \<noteq> y" "w \<noteq> z" "x \<noteq> y" "x \<noteq> z" "y \<noteq> z"
    using N by (simp_all add: wxyz vec_of_list_inject)

  have [simp]: "card J = 4" by simp

  have [simp]:
    "w $ to_index 0 = u" "w $ to_index (Suc 0) = u"
    "x $ to_index 0 = u" "x $ to_index (Suc 0) = v"
    "y $ to_index 0 = v" "y $ to_index (Suc 0) = u"
    "z $ to_index 0 = v" "z $ to_index (Suc 0) = v"
    using N by (simp_all add: wxyz nth_vec.rep_eq vec_of_list_inverse to_from_index)

  (* unpack the definition of tb_H w | tb_H x | tb_H y | tb_H z *)
  have rw: "
    xor_fold (map (\<lambda>i. h i ((a # b # u_n) ! from_index (to_index i :: 'n))) [0..<CARD('n)]) =
      h 0 a \<oplus>
      h (Suc 0) b \<oplus>
      xor_fold (map (\<lambda>i. h i u) [Suc (Suc 0)..<CARD('n)])"
    (is "xor_fold ?a = _") for a b h
  proof -
    have "?a = h 0 a # h (Suc 0) b # map (\<lambda>i. h i u) [Suc (Suc 0) ..< CARD('n)]"
      using assms(1) by (auto simp: upt_conv_Cons to_from_index u_n_def)
    then show ?thesis by simp
  qed

  (* Preliminaries end *)

  have "\<not> prob_space.indep_vars ?tb_S (\<lambda>_. count_space UNIV) tb_H J"
  proof -
    have "measure_pmf.prob ?tb_S {h. \<forall>key\<in>J. tb_H key h = f key}
      \<noteq> 1/(card R * card R * card R * card R)" (is "?lhs \<noteq> \<dots>")
    proof (cases "f w \<oplus> f x \<oplus> f y \<oplus> f z = 0")
      case True

      text \<open>In this case, we want to show that the probability is $\frac{1}{R^3}$ and not $\frac{1}{R^4}$\<close>

      let ?a = "\<lambda>h. xor_fold (map (\<lambda>i. h i u) [Suc (Suc 0)..<CARD('n)])"

      have "?lhs = measure_pmf.prob ?tb_S {h.
        h 0 u \<oplus> h (Suc 0) u \<oplus> ?a h = f w \<and>
        h 0 u \<oplus> h (Suc 0) v \<oplus> ?a h = f x \<and>
        h 0 v \<oplus> h (Suc 0) u \<oplus> ?a h = f y \<and>
        h 0 v \<oplus> h (Suc 0) v \<oplus> ?a h = f z}"
        using N by (simp add: tb_H_def wxyz nth_vec.rep_eq vec_of_list_inverse rw to_from_index)

      also have "\<dots> = 1 / real (card R * card R * card R)"
        using assms(1) True by (auto intro!: prob_4_conv arg_cong[where f = xor_fold])

      finally show ?thesis using assms(3) by simp
    next
      case False
      (* In this case, we want to show that the probability is 0 because it is impossible *)
      have False if "tb_H w h = f w" "tb_H x h = f x" "tb_H y h = f y" "tb_H z h = f z" for h
      proof -
        have "tb_H w h \<oplus> tb_H x h \<oplus> tb_H y h \<oplus> tb_H z h = 0"
          using N by (simp add: tb_H_def wxyz nth_vec.rep_eq vec_of_list_inverse rw to_from_index ac_simps)
        then show False using that False by simp
      qed
      then have "?lhs = 0" by (auto simp: measure_pmf_zero_iff)
      then show ?thesis by simp
    qed

    moreover have "\<dots> = (\<Prod>key\<in>J. measure_pmf.prob ?tb_S {h. tb_H key h = f key})"
      using prob_tb_H_bin by fastforce

    ultimately show ?thesis
      by (intro measure_pmf.indep_vars_pmf_contrapos[where P = "\<lambda> x y. y = f x"]) simp_all
  qed

  then show ?thesis by (force simp: prob_space.k_wise_indep_vars_def prob_space_measure_pmf)
qed

theorem not_four_universal:
  assumes "CARD('n) > 1" \<comment> \<open>if n = 1, then tabulation hashing is 4-independent\<close>
          "card D \<ge> 2" \<comment> \<open>if D = {} or D = {x}, then it is impossible to obtain 4 distinct keys\<close>
          "card R > 1" \<comment> \<open>tabulation hashing is 4-independent otherwise\<close>
  shows "\<not> prob_space.k_universal (tb_S n) 4 tb_H D\<^sup>n R"
  using not_four_indep[OF assms]
  by (simp add: prob_space.k_universal_def measure_pmf.prob_space_axioms)

end (* locale simple_tabulation_hashing *)

section \<open>Appendix\<close>
subsection \<open>Utility\<close>

context prob_space
begin

context
  fixes K D k p
  assumes assms': "K \<subseteq> D" "card K \<le> k" "finite K" "M = measure_pmf p"
begin

(* useful downstream lemma *)
lemma k_wise_indep_vars_probD:
  assumes "k_wise_indep_vars k (\<lambda>_. count_space UNIV) X D"
  shows "prob {\<omega>. \<forall>x\<in>K. P x (X x \<omega>)} = (\<Prod>x\<in>K. prob {\<omega>. P x (X x \<omega>)})"
  using assms' assms unfolding k_wise_indep_vars_def by (subst split_indep_events[of _ X K]) auto

(* useful downstream lemma *)
lemma
  assumes "k_universal k X D R"
  shows
    k_universal_probD:
      "\<And> P. prob {\<omega>. \<forall>x\<in>K. P x (X x \<omega>)} = (\<Prod>x\<in>K. prob {\<omega>. P x (X x \<omega>)})"
      (is "PROP ?thesis_0") and
    k_universal_probD':
      "prob {\<omega>. \<forall>x\<in>K. X x \<omega> = P x} = (\<Prod>x\<in>K. indicat_real R (P x) / real (card R))"
      (is ?thesis_1)
proof -
  from assms k_wise_indep_vars_probD show "PROP ?thesis_0"
    unfolding k_universal_def by fastforce
  from this[of "\<lambda> x y. y = P x"] uniform_onD[where A = R and B = "{P _}"] assms' assms
  show ?thesis_1
    unfolding k_universal_def
    by (auto intro!: prod.cong split: split_indicator simp: prob_space_measure_pmf)
qed

end
end (* prob_space *)

(* wrapper around simple_tabulation_hashing *)
locale simple_tabulation_hashing' = simple_tabulation_hashing +
  assumes r: "r = TYPE('result::{finite,abel_group_xor})"
  assumes q: "q = TYPE('q::index1)"
  assumes d: "d = TYPE('fragment::finite)"
begin

end (*locale simple_tabulation_hashing'*)

subsection \<open>Alternate proof of non-4-universal\<close>

subsubsection \<open>Preliminaries\<close>

lemma (in prob_space) finite_if_k_universal:
  assumes "k_universal k X D R" "D \<noteq> {}"
  shows "finite R"
  using assms by (auto simp add: k_universal_def uniform_on_def)

(* we settle on using functions to represent a vector *)
lemma xor_sum_uniform:
  fixes \<alpha> :: "'a :: {finite,abel_group_xor}"
  defines "R \<equiv> UNIV"
  assumes [simp]: "finite J" "J \<noteq> {}"
  shows "measure_pmf.prob (pmf_of_set (J \<rightarrow>\<^sub>E R)) {f. (\<Oplus>x\<in>J. f x) = \<alpha>} = 1 / real CARD('a)"
  (is "?lhs = ?rhs")
proof -
  note finite_PiE[simp] PiE_eq_empty_iff[simp] measure_pmf_single[simp]

  obtain a where a: "a \<in> J" and bij: "bij_betw (\<lambda>(f, v). f(a := v)) ((J - {a} \<rightarrow>\<^sub>E R) \<times> R) (J \<rightarrow>\<^sub>E R)"
    using bij_betw_funcsetE.bij_PiE_remove_point[of _ J R] assms(3) by blast

  have [simp]: "R \<noteq> {}" using assms(1) by blast

  have [simp]: "set_pmf (pmf_of_set (J \<rightarrow>\<^sub>E R)) = J \<rightarrow>\<^sub>E R"
               "set_pmf (pmf_of_set (J - {a} \<rightarrow>\<^sub>E R)) = J - {a} \<rightarrow>\<^sub>E R"
               "set_pmf (pmf_of_set R) = R"
    by (auto intro!: set_pmf_of_set)

  let ?destructure =
    "(pair_pmf (pmf_of_set (J - {a} \<rightarrow>\<^sub>E R))
       (pmf_of_set R))"

  have asmap: "pmf_of_set (J \<rightarrow>\<^sub>E R) = map_pmf (\<lambda>(f, v). f(a := v)) ?destructure"
    using assms bij by (simp flip: pmf_of_set_prod_eq map_pmf_of_set_bij_betw
                              del: PiE_UNIV UNIV_Times_UNIV)

  have "?lhs = measure_pmf.prob (pmf_of_set (J \<rightarrow>\<^sub>E R)) {f\<in>J \<rightarrow>\<^sub>E R. (\<Oplus>x\<in>J. f x) = \<alpha>}"
    apply (subst measure_Int_set_pmf[symmetric])
    by (auto intro!: arg_cong[where ?f = "measure_pmf.prob _"])

  also have "\<dots> =
    measure_pmf.prob ?destructure
      (Sigma (J - {a} \<rightarrow>\<^sub>E R) (\<lambda>f. {x. x \<oplus> (\<Oplus>x\<in>J - {a}. f x) = \<alpha>}))"
    using PiE_fun_upd a by (auto simp add: asmap xor_sum.remove[where ?x = a, OF assms(2) a]
                                 intro!: measure_pmf_cong)

  also have "\<dots> =
    measure_pmf.prob ?destructure
      (Sigma (J - {a} \<rightarrow>\<^sub>E R) (\<lambda>f. {\<alpha> \<oplus> (\<Oplus>x\<in>J- {a}. f x)}))"
    by (fastforce intro: measure_pmf_cong simp add: ac_simps)

  also have "\<dots> = ?rhs"
    by (simp add: assms(1) measure_pmf_prob_dependent_product_bound_eq' measure_pmf_of_set)

  finally show "?lhs = ?rhs" .
qed

(* we used \<open>D \<noteq> {}\<close> instead of \<open>J \<noteq> {}\<close> because it is more general *)
(* card J \<noteq> 0 implies finite J as well *)
lemma k_universal_conv_pmf_of_set:
  defines "R \<equiv> UNIV" (* to figure out if we can allow R \<subseteq> UNIV *)
  assumes "prob_space.k_universal (measure_pmf p) k X D R"
      and "J \<subseteq> D" "card J \<le> k" "finite J" "D \<noteq> {}"
  shows "map_pmf (\<lambda>\<omega>. \<lambda>x\<in>J. X x \<omega>) p = pmf_of_set (J \<rightarrow>\<^sub>E R)"
proof (intro pmf_eqI)
  fix P
  from assms(2) have fR: "finite R" by (simp add: assms(6) measure_pmf.finite_if_k_universal)

  {
    assume P: "P \<in> J \<rightarrow>\<^sub>E R"

    have "pmf (map_pmf (\<lambda>\<omega>. \<lambda>x\<in>J. X x \<omega>) p) P = measure_pmf.prob p {\<omega>. (\<lambda>x\<in>J. X x \<omega>) = P}"
      by (simp add: pmf_map vimage_def)

    also have "\<dots> = measure_pmf.prob p {\<omega>. \<forall>x\<in>J. X x \<omega> = P x}"
      using P by (fastforce intro: arg_cong[where ?f = "measure_pmf.prob _"])

    also have "\<dots> = (\<Prod>x\<in>J. indicat_real R (P x) / real (card R))"
      using assms by (simp add: measure_pmf.k_universal_probD')

    also have "\<dots> = (1 / real (card R)) ^ card J"
      apply (subst prod.cong[where ?B= J and ?h = "\<lambda>_. 1 / real (card R)"]; simp)
      by (metis P indicator_simps(1) PiE_E)

    also have "\<dots> = indicat_real (J \<rightarrow>\<^sub>E R) P / real (card (J \<rightarrow>\<^sub>E R))"
      by (simp add: P assms(5) card_funcsetE power_one_over)

    also have "\<dots> = pmf (pmf_of_set (J \<rightarrow>\<^sub>E R)) P"
      using P by (subst pmf_of_set) (auto simp add: assms(5) fR finite_PiE)

    finally have "pmf (map_pmf (\<lambda>\<omega>. \<lambda>x\<in>J. X x \<omega>) p) P = pmf (pmf_of_set (J \<rightarrow>\<^sub>E R)) P" .
  }

  moreover {
    assume P: "P \<notin> J \<rightarrow>\<^sub>E R"

    have "pmf (map_pmf (\<lambda>\<omega>. \<lambda>x\<in>J. X x \<omega>) p) P = measure_pmf.prob p {\<omega>. (\<lambda>x\<in>J. X x \<omega>) = P}"
      by (simp add: pmf_map vimage_def)

    also have "\<dots> = 0"
    proof (subst measure_pmf_zero_iff)
      have "{\<omega>. (\<lambda>x\<in>J. X x \<omega>) = P} = {}"
        using P assms(1) (* using R \<equiv> UNIV for now *)
        by (auto simp add: measure_pmf.prob_space_axioms prob_space.k_universal_def)

      then show "set_pmf p \<inter> {\<omega>. (\<lambda>x\<in>J. X x \<omega>) = P} = {}" by blast
    qed

    also have "\<dots> = pmf (pmf_of_set (J \<rightarrow>\<^sub>E R)) P"
      apply (rule sym)
      apply (subst pmf_eq_0_set_pmf)
      apply (subst set_pmf_of_set)
      subgoal by (simp add: PiE_eq_empty_iff assms(1))
      subgoal by (simp add: assms(5) fR finite_PiE)
      using P .

    finally have "pmf (map_pmf (\<lambda>\<omega>. \<lambda>x\<in>J. X x \<omega>) p) P = pmf (pmf_of_set (J \<rightarrow>\<^sub>E R)) P" .
  }

  ultimately show "pmf (map_pmf (\<lambda>\<omega>. \<lambda>x\<in>J. X x \<omega>) p) P = pmf (pmf_of_set (J \<rightarrow>\<^sub>E R)) P" by blast
qed

lemma (*tag:important*) k_universal_imp_xor_sum_uniform:
  fixes \<alpha> :: "'a :: {finite,abel_group_xor}"
  defines "R \<equiv> UNIV"
  assumes "prob_space.k_universal (measure_pmf p) k X D R"
      and "J \<subseteq> D" "card J \<le> k" "finite J" "J \<noteq> {}"
  shows "measure_pmf.prob p {\<omega>. (\<Oplus>x\<in>J. X x \<omega>) = \<alpha>} = 1 / real (card R)"
  (is "?lhs = ?rhs")
proof -
  have "?lhs = measure_pmf.prob (map_pmf (\<lambda>\<omega>. \<lambda>x\<in>J. X x \<omega>) p) {f. (\<Oplus>x\<in>J. f x) = \<alpha>}" by simp
  also have "\<dots> = measure_pmf.prob (pmf_of_set (J \<rightarrow>\<^sub>E R)) {f. (\<Oplus>x\<in>J. f x) = \<alpha>}"
    using assms by (intro arg_cong2[where ?f = "measure_pmf.prob"])
                   (auto intro!: k_universal_conv_pmf_of_set)
  also have "\<dots> = ?rhs" using assms by (auto intro!: xor_sum_uniform)
  finally show "?lhs = ?rhs" .
qed

subsubsection \<open>Proofs\<close>

context simple_tabulation_hashing begin

lemma k_wise_indep_vars_imp_xor_sum_uniform:
  assumes "prob_space.k_wise_indep_vars (tb_S n) k (\<lambda>_. count_space R) tb_H D\<^sup>n"
          "J \<noteq> {}" "card J \<le> k"
  shows "measure_pmf.prob (tb_S n) {h. (\<Oplus>x\<in>J. tb_H x h) = \<alpha>} = 1 / real (card R)"
  using assms
  by (auto
    intro: k_universal_imp_xor_sum_uniform[where ?k = k and ?D = "D\<^sup>n"]
    simp: prob_space.k_universal_def prob_space_measure_pmf uniform)

lemma not_k_wise_indep_vars_by_xor_sum:
  assumes "measure_pmf.prob (tb_S n) {h. (\<Oplus>x\<in>J. tb_H x h) = \<alpha>} \<noteq> 1 / real (card R)"
          "J \<noteq> {}" "card J \<le> k"
  shows "\<not> prob_space.k_wise_indep_vars (tb_S n) k (\<lambda>_. count_space R) tb_H D\<^sup>n"
  using assms(1) apply (rule contrapos_nn)
  using assms by (simp add: k_wise_indep_vars_imp_xor_sum_uniform)

lemma not_four_indep':
  assumes "CARD('n) > 1" \<comment> \<open>if n = 1, then tabulation hashing is 4-independent\<close>
          "card D \<ge> 2" \<comment> \<open>if D = {} or D = {x}, then it is impossible to obtain 4 distinct keys\<close>
          "card R > 1" \<comment> \<open>tabulation hashing is 4-independent otherwise\<close>
  shows "\<not> prob_space.k_wise_indep_vars (tb_S n) 4 (\<lambda>_. count_space R) tb_H D\<^sup>n"
proof -
  obtain u v :: "'fragment" where pq [simp]: "u \<noteq> v" by (meson assms(2) UNIV_I card_2_iff' ex_card)
  define u_n where "u_n \<equiv> replicate (CARD('n) - 2) u"
  let ?w = "u # u # u_n"
  let ?x = "u # v # u_n"
  let ?y = "v # u # u_n"
  let ?z = "v # v # u_n"

  define w x y z :: "('fragment, 'n) vec" where wxyz:
    "w = vec_of_list ?w" "x = vec_of_list ?x" "y = vec_of_list ?y" "z = vec_of_list ?z"
  define J where [simp]: "J = {w,x,y,z}"

  have N: "a # b # u_n \<in> {xs. length xs = CARD('n)}" for a b
    using assms(1) by (simp add: u_n_def)

  have [simp]: "w \<noteq> x" "w \<noteq> y" "w \<noteq> z" "x \<noteq> y" "x \<noteq> z" "y \<noteq> z"
    using N by (simp_all add: vec_of_list_inject wxyz)

  have [simp]: "card J = 4" by simp

  (* unpack the definition of tb_H w | tb_H x | tb_H y | tb_H z *)
  have rw: "
    xor_fold (map (\<lambda>i. h i ((a # b # u_n) ! from_index (to_index i :: 'n))) [0..<CARD('n)]) =
      h 0 a \<oplus>
      h (Suc 0) b \<oplus>
      xor_fold (map (\<lambda>i. h i u) [Suc (Suc 0)..<CARD('n)])"
    (is "xor_fold ?a = _") for a b h
  proof -
    have "?a = h 0 a # h (Suc 0) b # map (\<lambda>i. h i u) [Suc (Suc 0) ..< CARD('n)]"
      using assms(1) by (auto simp: upt_conv_Cons to_from_index u_n_def)
    then show ?thesis by simp
  qed

  from N have "measure_pmf.prob (tb_S n) {h. (\<Oplus>x\<in>J. tb_H x h) = 0} = 1"
    apply (simp add: tb_H_def nth_vec.rep_eq del: eq_iff)
    by (simp add: wxyz nth_vec.rep_eq vec_of_list_inverse rw ac_simps)

  then show ?thesis
    using assms(3) by (intro not_k_wise_indep_vars_by_xor_sum[of J 0]) simp_all
qed
end (* context simple_tabulation_hashing *)
end (* theory *)