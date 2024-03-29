section \<open> Certificate-based ApproxMC \<close>

text \<open> This turns the randomized algorithm into an
  executable certificate checker \<close>

theory CertCheck
imports ApproxMCAnalysis

begin

subsection \<open> ApproxMC with lists instead of sets \<close>

type_synonym 'a xor = "'a list \<times> bool"

definition satisfies_xorL :: "'a xor \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool"
  where "satisfies_xorL xb \<omega> =
    even (sum_list (map (of_bool \<circ> \<omega>) (fst xb)) +
      of_bool (snd xb)::nat)"

(* Extract a sublist based on bits *)
definition sublist_bits::"'a list \<Rightarrow> bool list \<Rightarrow> 'a list"
  where "sublist_bits ls bs =
    map fst (filter snd (zip ls bs))"

definition xor_from_bits::
  "'a list \<Rightarrow> bool list \<times> bool \<Rightarrow> 'a xor"
  where "xor_from_bits V xsb =
    (sublist_bits V (fst xsb), snd xsb)"

locale ApproxMCL =
  fixes sols :: "'fml \<Rightarrow> ('a \<Rightarrow> bool) set"
  fixes enc_xor :: "'a xor \<Rightarrow> 'fml \<Rightarrow> 'fml"
  assumes sols_enc_xor:
    "\<And>F xor.
      sols (enc_xor xor F) =
      sols F \<inter> {\<omega>. satisfies_xorL xor \<omega>}"
begin

definition list_of_set ::"'a set \<Rightarrow> 'a list"
where "list_of_set x = (@ls. set ls = x \<and> distinct ls)"

definition xor_conc :: "'a set \<times> bool \<Rightarrow> 'a xor"
  where "xor_conc xsb = (list_of_set (fst xsb), snd xsb)"

definition enc_xor_conc :: "'a set \<times> bool \<Rightarrow> 'fml \<Rightarrow> 'fml"
  where "enc_xor_conc = enc_xor \<circ> xor_conc"

lemma distinct_count_list:
  assumes "distinct ls"
  shows "count_list ls x = of_bool (x \<in> set ls)"
  using assms
  apply (induction ls)
  by auto

lemma list_of_set:
  assumes "finite x"
  shows "distinct (list_of_set x)" "set (list_of_set x) = x"
  unfolding list_of_set_def
  by (metis (mono_tags, lifting) assms finite_distinct_list someI_ex)+

lemma count_list_list_of_set:
  assumes "finite x"
  shows "count_list (list_of_set x) y = of_bool (y \<in> x)"
  apply (subst distinct_count_list)
  using list_of_set[OF assms]
  by auto

lemma satisfies_xorL_xor_conc:
  assumes "finite x"
  shows"satisfies_xorL (xor_conc (x,b)) \<omega> \<longleftrightarrow> satisfies_xor (x,b) {x. \<omega> x}"
  unfolding satisfies_xorL_def xor_conc_def
  using list_of_set[OF assms]
  by (auto simp add: sum_list_map_eq_sum_count count_list_list_of_set[OF assms] Int_ac(3) assms)

sublocale appmc: ApproxMC sols enc_xor_conc
  apply unfold_locales
  unfolding enc_xor_conc_def o_def
  apply (subst sols_enc_xor)
  using satisfies_xorL_xor_conc by fastforce

definition size_xorL ::"
  'fml \<Rightarrow> 'a list \<Rightarrow>
  (nat \<Rightarrow> bool list \<times> bool) \<Rightarrow>
  nat \<Rightarrow> nat"
  where "size_xorL F S xorsl i = (
    let xors = map (xor_from_bits S \<circ> xorsl) [0..<i] in
    let Fenc = fold enc_xor xors F in
      card (proj (set S) (sols Fenc)))"

definition check_xorL ::"
  'fml \<Rightarrow> 'a list \<Rightarrow>
  nat \<Rightarrow>
  (nat \<Rightarrow> bool list \<times> bool) \<Rightarrow>
  nat \<Rightarrow> bool"
  where "check_xorL F S thresh xorsl i =
  (size_xorL F S xorsl i < thresh)"

definition approxcore_xorsL :: "
  'fml \<Rightarrow> 'a list \<Rightarrow>
  nat \<Rightarrow>
  (nat \<Rightarrow> (bool list \<times> bool)) \<Rightarrow>
  nat"
  where "
    approxcore_xorsL F S thresh xorsl =
    (case List.find
      (check_xorL F S thresh xorsl) [1..<length S] of
      None \<Rightarrow> 2 ^ length S
    | Some m \<Rightarrow>
      (2 ^ m * size_xorL F S xorsl m))"

definition xor_abs :: "'a xor \<Rightarrow> 'a set \<times> bool"
  where "xor_abs xsb = (set (fst xsb), snd xsb)"

lemma sols_fold_enc_xor:
  assumes "list_all2 (\<lambda>x y.
    \<forall>w. satisfies_xorL x w = satisfies_xorL y w) xs ys"
  assumes "sols F = sols G"
  shows "sols (fold enc_xor xs F) = sols (fold enc_xor ys G)"
  using assms
proof (induction xs arbitrary: ys F G)
  case Nil
  then show ?case
    by auto
  next
  case (Cons x xss)
  then obtain y yss where ys: "ys = y#yss"
  by (meson list_all2_Cons1)
  have all2: "\<forall>w. satisfies_xorL x w = satisfies_xorL y w"
    using Cons.prems(1) ys by blast
  have *: "sols (enc_xor x F) = sols (enc_xor y G)"
    apply (subst sols_enc_xor)
    using all2 local.Cons(3) sols_enc_xor by presburger
  then show ?case unfolding ys
  using "*" Cons.IH Cons.prems(2) local.Cons(2) local.Cons(3) ys by auto
qed

lemma satisfies_xor_xor_abs:
  assumes "distinct x"
  shows"satisfies_xor (xor_abs (x,b)) {x. \<omega> x} \<longleftrightarrow> satisfies_xorL (x,b) \<omega>"
  unfolding satisfies_xorL_def xor_abs_def
  apply (clarsimp simp add: sum_list_map_eq_sum_count)
  by (smt (verit, ccfv_SIG) IntD1 Int_commute assms card_eq_sum distinct_count_list of_bool_eq(2) sum.cong)

lemma xor_conc_xor_abs_rel:
  assumes "distinct (fst x)"
  shows"satisfies_xorL (xor_conc (xor_abs x)) w \<longleftrightarrow>
    satisfies_xorL x w"
  unfolding xor_abs_def
  apply (subst satisfies_xorL_xor_conc)
  subgoal by (simp add: xor_abs_def[symmetric])
  using assms satisfies_xor_xor_abs xor_abs_def by auto

lemma sorted_sublist_bits:
  assumes "sorted V"
  shows"sorted (sublist_bits V bs)"
  unfolding sublist_bits_def
  using assms
  by (auto intro!: sorted_filter sorted_wrt_take simp add: map_fst_zip_take)

lemma distinct_sublist_bits:
  assumes "distinct V"
  shows"distinct (sublist_bits V bs)"
  unfolding sublist_bits_def
  using assms
  by (auto intro!: distinct_map_filter simp add: map_fst_zip_take)

lemma distinct_fst_xor_from_bits:
  assumes "distinct V"
  shows"distinct (fst (xor_from_bits V bs))"
  unfolding xor_from_bits_def
  using distinct_sublist_bits[OF assms]
  by auto

lemma size_xorL:
  assumes "\<And>j. j < i \<Longrightarrow>
    xorsf j =
    Some (xor_abs (xor_from_bits S (xorsl j)))"
  assumes "distinct S"
  shows "size_xorL F S xorsl i =
    appmc.size_xor F (set S) xorsf i"
  unfolding appmc.size_xor_def size_xorL_def
  apply (clarsimp simp add: enc_xor_conc_def fold_map[symmetric])
  apply (intro arg_cong[where f = "(\<lambda>x. card (proj (set S) x))"])
  apply (intro sols_fold_enc_xor)
  by (auto simp add: list_all2_map1 list_all2_map2 list_all2_same assms(1) assms(2) distinct_fst_xor_from_bits xor_conc_xor_abs_rel)

lemma fold_enc_xor_more:
  assumes "x \<in> sols (fold enc_xor (xs @ rev ys) F)"
  shows "x \<in> sols (fold enc_xor xs F)"
  using assms
proof (induction ys arbitrary: F)
  case Nil
  then show ?case
    by auto
next
  case ih: (Cons y ys)
  show ?case
    using ih by (auto simp add: ih.prems(1) sols_enc_xor)
qed

lemma size_xorL_anti_mono:
  assumes "x \<le> y" "distinct S"
  shows "size_xorL F S xorsl x \<ge> size_xorL F S xorsl y"
proof -
  obtain ys where ys: "[0..<y] = [0..<x] @ ys" "distinct ys"
  by (metis assms(1) bot_nat_0.extremum distinct_upt ordered_cancel_comm_monoid_diff_class.add_diff_inverse upt_add_eq_append)

  define rys where"rys = (rev (map (xor_from_bits S \<circ> xorsl) ys))"
  have *: "\<And>y. y \<in> set rys \<Longrightarrow> distinct (fst y)"
    unfolding rys_def
    using assms(2) distinct_fst_xor_from_bits
    by (metis (no_types, opaque_lifting) ex_map_conv o_apply set_rev)

  show ?thesis
    unfolding size_xorL_def Let_def
  apply (intro card_mono proj_mono)
  subgoal using card_proj(1) by blast
  unfolding ys
  by (metis fold_enc_xor_more map_append rev_rev_ident subsetI)
qed

lemma find_upto_SomeI:
  assumes "\<And>i. a \<le> i \<Longrightarrow> i < x \<Longrightarrow> \<not>P i"
  assumes "P x" "a \<le> x" "x < b"
  shows "find P [a..<b] = Some x"
proof -
  have x: "[a..<b] ! (x-a) = x"
    by (simp add: assms(3) assms(4))
  have j: "\<And>j. j<x-a \<Longrightarrow> \<not> P ([a..<b] ! j)"
    using assms(1) assms(4) by auto
  show ?thesis
  unfolding find_Some_iff
  using x j
  by (metis assms(2) assms(3) assms(4) diff_less_mono length_upt)
qed

lemma check_xorL:
  assumes "\<And>j. j < i \<Longrightarrow>
    xorsf j =
    Some (xor_abs (xor_from_bits S (xorsl j)))"
  assumes "distinct S"
  shows "check_xorL F S thresh xorsl i =
    appmc.check_xor F (set S) thresh xorsf i"
  unfolding appmc.check_xor_def check_xorL_def
  using size_xorL[OF assms] by presburger

lemma approxcore_xorsL:
  assumes "\<And>j. j < length S - 1  \<Longrightarrow>
    xorsf j =
    Some (xor_abs (xor_from_bits S (xorsl j)))"
  assumes S: "distinct S"
  shows "approxcore_xorsL F S thresh xorsl =
    appmc.approxcore_xors F (set S) thresh xorsf"
proof -
  have c:"card (set S) = length S" using S
  by (simp add: distinct_card)

  have *: "find (check_xorL F S thresh xorsl) [1..<length S] =
   find (appmc.check_xor F (set S) thresh xorsf) [1..<card (set S)]"
    unfolding c
    by (auto intro!: find_cong check_xorL[OF assms(1) S])

  have **: "find (appmc.check_xor F
                  (set S) thresh xorsf)
            [Suc 0..<length S] =
           Some a \<Longrightarrow>
           j < a \<Longrightarrow>
           xorsf j =
           Some
            (xor_abs
              (xor_from_bits S
                (xorsl j)))" for a j
    unfolding find_Some_iff
    by (auto simp add: assms(1))
  show ?thesis
  unfolding appmc.approxcore_xors_def approxcore_xorsL_def * c
  apply (cases "find (appmc.check_xor F (set S) thresh xorsf)
           [Suc 0..<length S]")
  subgoal by clarsimp
  by (auto intro!: ApproxMCL.size_xorL simp add: ApproxMCL_axioms assms **)
qed

definition approxmc_mapL::"
  'fml \<Rightarrow> 'a list \<Rightarrow>
  real \<Rightarrow> real \<Rightarrow> nat \<Rightarrow>
  (nat \<Rightarrow> nat \<Rightarrow> (bool list \<times> bool)) \<Rightarrow>
  nat"
  where "approxmc_mapL F S \<epsilon> \<delta> n xorsLs = (
    let \<epsilon> = appmc.mk_eps \<epsilon> in
    let thresh = appmc.compute_thresh \<epsilon> in
    if card (proj (set S) (sols F)) < thresh then
      card (proj (set S) (sols F))
    else
      let t = appmc.compute_t \<delta> n in
      median t (approxcore_xorsL F S thresh \<circ> xorsLs))"

definition random_xorB :: "nat \<Rightarrow> (bool list \<times> bool) pmf"
  where "random_xorB n =
    pair_pmf
      (replicate_pmf n (bernoulli_pmf (1/2)))
      (bernoulli_pmf (1/2))"

(* Actually, we can restrict i too *)
lemma approxmc_mapL:
  assumes "\<And>i j. j < length S - 1 \<Longrightarrow>
    xorsFs i j =
    Some (xor_abs (xor_from_bits S (xorsLs i j)))"
  assumes S: "distinct S"
  shows "
    approxmc_mapL F S \<epsilon> \<delta> n xorsLs =
    appmc.approxmc_map F (set S) \<epsilon> \<delta> n xorsFs"
proof -
  show ?thesis
    unfolding approxmc_mapL_def appmc.approxmc_map_def Let_def
    using assms by (auto intro!: median_cong approxcore_xorsL)
qed

lemma approxmc_mapL':
  assumes S: "distinct S"
  shows "
    approxmc_mapL F S \<epsilon> \<delta> n xorsLs =
    appmc.approxmc_map F (set S) \<epsilon> \<delta> n
      (\<lambda>i j. if j < length S - 1
         then Some (xor_abs (xor_from_bits S (xorsLs i j)))
         else None)"
  apply (intro approxmc_mapL)
  using assms by auto

lemma bits_to_random_xor:
  assumes "distinct S"
  shows "map_pmf
    (\<lambda>x. xor_abs (xor_from_bits S x))
    (random_xorB (length S)) =
    random_xor (set S)"
proof -
  have "xor_abs (xor_from_bits S (a,b)) = apfst (set \<circ> sublist_bits S) (a,b)" for a b
   using xor_abs_def by (auto simp add: xor_from_bits_def)

  then have *: "(\<lambda>x. xor_abs (xor_from_bits S x)) = apfst (set \<circ> sublist_bits S)"
    by auto

  have "\<And>x. x \<in> set S \<Longrightarrow>
         z x \<Longrightarrow>
         \<exists>b. (\<exists>n. S ! n = x \<and>
                  map z S ! n = b \<and>
                  n < length S) \<and> b" for z
    by (metis assms distinct_Ex1 nth_map)

  then have " set (map fst
               (filter snd
                 (zip S (map z S)))) =
         {x \<in> set S. Some (z x) = Some True}" for z
    by (auto elim: in_set_zipE simp add: in_set_zip image_def )

  then have **: "map_pmf (set \<circ> sublist_bits S)
       (replicate_pmf (length S) (bernoulli_pmf (1 / 2))) =
    map_pmf (\<lambda>b. {x \<in> set S. b x = Some True})
       (Pi_pmf (set S) (Some undefined)
         (\<lambda>_. map_pmf Some (bernoulli_pmf (1 / 2))))"
    apply (subst replicate_pmf_Pi_pmf[OF assms, where def = "undefined"])
    apply (subst Pi_pmf_map[of _  _ "undefined"])
    subgoal by (auto intro!: pmf.map_cong0 simp add: map_pmf_comp sublist_bits_def)
    subgoal by (meson set_zip_leftD)
    unfolding map_pmf_comp sublist_bits_def o_def
    by (auto intro!: pmf.map_cong0)

  show ?thesis
    unfolding random_xorB_def
    apply (subst random_xor_from_bits)
    by (auto simp add: * ** pair_map_pmf1[symmetric])
qed

lemma Pi_pmf_map_pmf_Some:
  assumes "finite S"
  shows "Pi_pmf S None (\<lambda>_. map_pmf Some p) =
    map_pmf (\<lambda>f v. if v \<in> S then Some (f v) else None)
    (Pi_pmf S def (\<lambda>_. p))"
proof -
  have *: "Pi_pmf S None (\<lambda>_. map_pmf Some p) =
    map_pmf (\<lambda>f x. if x \<in> S then f x else None)
    (Pi_pmf S (Some def) (\<lambda>_. map_pmf Some p))"
    apply (subst Pi_pmf_default_swap[OF assms])
      by auto

  show ?thesis unfolding *
    apply (subst Pi_pmf_map[OF assms, of  _ def])
    subgoal by simp
    apply (simp add: map_pmf_comp o_def )
    by (metis comp_eq_dest_lhs)
qed

lemma bits_to_random_xors:
  assumes "distinct S"
  shows "
    map_pmf
    (\<lambda>f j.
      if j < n
      then Some (xor_abs (xor_from_bits S (f j)))
      else None)
    (Pi_pmf {..<(n::nat)} def (\<lambda>_. random_xorB (length S))) =
    random_xors (set S) n"
  unfolding random_xors_def
  apply (subst Pi_pmf_map_pmf_Some)
  subgoal using assms by simp
  apply (subst bits_to_random_xor[symmetric, OF assms])
  apply (subst Pi_pmf_map[where dflt = "def", where dflt'="xor_abs (xor_from_bits S def)"])
  subgoal by simp
  subgoal by simp
  apply (clarsimp simp add: map_pmf_comp o_def)
  by (metis o_apply)

lemma bits_to_all_random_xors:
  assumes "distinct S"
  assumes "(\<lambda>j. if j < n
          then Some (xor_abs (xor_from_bits S (def1 j)))
          else None) = def"
  shows "
    map_pmf
    ((\<circ>) (\<lambda>f j. if j < n
                 then Some (xor_abs (xor_from_bits S (f j)))
                 else None))
    (Pi_pmf {0..<(m::nat)} def1
      (\<lambda>_.
        Pi_pmf {..<(n::nat)} def2 (\<lambda>_. random_xorB (length S)))) =
    Pi_pmf {0..<m} def
         (\<lambda>i. random_xors (set S) n)"
  apply (subst bits_to_random_xors[symmetric, OF assms(1), of _ "def2"])
  apply (subst Pi_pmf_map[OF _])
  using assms(2) by auto

(* Sample t * (l-1) * l XORs *)
definition random_seed_xors::"nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> bool list \<times> bool) pmf"
  where "random_seed_xors t l =
    (prod_pmf {0..<t}
      (\<lambda>_. prod_pmf {..<l-1} (\<lambda>_. random_xorB l)))"

lemma approxmcL_sound:
  assumes \<delta>: "\<delta> > 0" "\<delta> < 1"
  assumes \<epsilon>: "\<epsilon> > 0"
  assumes S: "distinct S"
  shows "
    prob_space.prob
      (map_pmf (approxmc_mapL F S \<epsilon> \<delta> n)
        (random_seed_xors (appmc.compute_t \<delta> n) (length S)))
      {c. real c \<in>
        {real (card (proj (set S) (sols F))) / (1 + \<epsilon>)..
          (1 + \<epsilon>) * real (card (proj (set S) (sols F)))}}
      \<ge> 1 - \<delta>"
proof -
  define def where "def =
      (\<lambda>j. if j < degree S
          then Some (xor_abs (xor_from_bits S (undefined j)))
          else None)"
  have *: "(map_pmf (approxmc_mapL F S \<epsilon> \<delta> n)
        (Pi_pmf {0..<appmc.compute_t \<delta> n} undefined
           (\<lambda>_. Pi_pmf {..<length S - 1} undefined
            (\<lambda>_. random_xorB (length S))))) =
     (map_pmf (appmc.approxmc_map F (set S) \<epsilon> \<delta> n)
      (map_pmf ((\<circ>) (\<lambda>f.
          (\<lambda>j. if j < length S - 1
                 then Some (xor_abs (xor_from_bits S (f j)))
                 else None)))
       (Pi_pmf {0..<appmc.compute_t \<delta> n} undefined
         (\<lambda>_. Pi_pmf {..<length S - 1} undefined
                (\<lambda>_. random_xorB (length S))))))"
    unfolding approxmc_mapL'[OF S]
    by (simp add: map_pmf_comp o_def)
  have **: "
    (map_pmf (approxmc_mapL F S \<epsilon> \<delta> n)
        (Pi_pmf {0..<appmc.compute_t \<delta> n} undefined
           (\<lambda>_. Pi_pmf {..<length S - 1} undefined
            (\<lambda>_. random_xorB (length S))))) =
    map_pmf (appmc.approxmc_map F (set S) \<epsilon> \<delta> n)
     (Pi_pmf {0..<appmc.compute_t \<delta> n} def
       (\<lambda>i. random_xors (set S) (card (set S) - 1)))"
    unfolding *
    apply (subst bits_to_all_random_xors[OF S])
    using def_def
    by (auto simp add: assms(4) distinct_card)
  show ?thesis
    unfolding ** appmc.approxmc_map_eq random_seed_xors_def
    using \<delta>(2) \<epsilon> appmc.approxmc'_sound assms(1) by blast
qed

(* This is more convenient for stating what happens when
  certification returns the "wrong" result *)
lemma approxmcL_sound':
  assumes \<delta>: "\<delta> > 0" "\<delta> < 1"
  assumes \<epsilon>: "\<epsilon> > 0"
  assumes S: "distinct S"
  shows "
    prob_space.prob
      (map_pmf (approxmc_mapL F S \<epsilon> \<delta> n)
        (random_seed_xors (appmc.compute_t \<delta> n) (length S)))
      {c. real c \<notin>
        {real (card (proj (set S) (sols F))) / (1 + \<epsilon>)..
          (1 + \<epsilon>) * real (card (proj (set S) (sols F)))}} \<le> \<delta>"
proof -
  have "prob_space.prob
      (map_pmf (approxmc_mapL F S \<epsilon> \<delta> n)
        (Pi_pmf {0..<appmc.compute_t \<delta> n} undefined
           (\<lambda>_. Pi_pmf {..<length S - 1} undefined
            (\<lambda>_. random_xorB (length S)))))
      {c. real c \<notin>
        {real (card (proj (set S) (sols F))) / (1 + \<epsilon>)..
          (1 + \<epsilon>) * real (card (proj (set S) (sols F)))}} =
    1 - prob_space.prob
      (map_pmf (approxmc_mapL F S \<epsilon> \<delta> n)
        (Pi_pmf {0..<appmc.compute_t \<delta> n} undefined
           (\<lambda>_. Pi_pmf {..<length S - 1} undefined
            (\<lambda>_. random_xorB (length S)))))
      {c. real c \<in>
        {real (card (proj (set S) (sols F))) / (1 + \<epsilon>)..
          (1 + \<epsilon>) * real (card (proj (set S) (sols F)))}}"
    apply (subst measure_pmf.prob_compl[symmetric])
    by (auto simp add: vimage_def)
  thus ?thesis using approxmcL_sound[OF assms, of "F" "n"] \<delta>
    unfolding random_seed_xors_def
    by linarith
qed

end

subsection \<open> ApproxMC certificate checker \<close>

(* Helper functions *)
definition str_of_bool :: "bool \<Rightarrow> String.literal"
  where "str_of_bool b = (
  if b then STR ''true'' else STR ''false'')"

fun str_of_nat_aux :: "nat \<Rightarrow> char list \<Rightarrow> char list"
  where "str_of_nat_aux n acc = (
  let c = char_of_integer (of_nat (48 + n mod 10)) in
  if n < 10 then c # acc
  else str_of_nat_aux (n div 10) (c # acc))"

definition str_of_nat :: "nat \<Rightarrow> String.literal"
  where "str_of_nat n = String.implode (str_of_nat_aux n [])"

type_synonym 'a sol = "('a \<times> bool) list"

(* The canonical assignment specified by a list *)
definition canon_map_of :: "('a \<times> bool) list \<Rightarrow> ('a \<Rightarrow> bool)"
  where "canon_map_of ls =
    (let m = map_of ls in
    (\<lambda>x. case m x of None \<Rightarrow> False | Some b \<Rightarrow> b))"

(* The canonical assignment specified by a list *)
lemma canon_map_of[code]:
  shows "canon_map_of ls =
    (let m = Mapping.of_alist ls in
     Mapping.lookup_default False m)"
  unfolding canon_map_of_def lookup_default_def
  by (auto simp add: lookup_of_alist)

definition proj_sol :: "'a list \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool list"
  where "proj_sol S w = map w S"

text \<open> The following extended locale assumes
  additional support for syntactically working with solutions \<close>
locale CertCheck = ApproxMCL sols enc_xor
  for sols :: "'fml \<Rightarrow> ('a \<Rightarrow> bool) set"
  and enc_xor :: "'a list \<times> bool \<Rightarrow> 'fml \<Rightarrow> 'fml" +
  fixes check_sol :: "'fml \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool"
  fixes ban_sol :: "'a sol \<Rightarrow> 'fml \<Rightarrow> 'fml"
  assumes sols_ban_sol:
    "\<And>F vs.
      sols (ban_sol vs F) =
      sols F \<inter> {\<omega>. map \<omega> (map fst vs) \<noteq> map snd vs}"
  assumes check_sol:
    "\<And>F w. check_sol F w \<longleftrightarrow> w \<in> sols F"
begin

text \<open> Assuming parameter access to an UNSAT checking oracle \<close>
context
  fixes check_unsat :: "'fml \<Rightarrow> bool"
begin

text \<open> Throughout this checker, INL indicates error, INR indicates success \<close>

definition check_BSAT_sols::"
  'fml \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> ('a \<Rightarrow> bool) list \<Rightarrow> String.literal + unit"
where "check_BSAT_sols F S thresh cms = (
  let ps = map (proj_sol S) cms in
  let b1 = list_all (check_sol F) cms in
  let b2 = distinct ps in
  let b3 =
    (length cms < thresh \<longrightarrow>
      check_unsat (fold ban_sol (map (zip S) ps) F)) in
    if b1 \<and> b2 \<and> b3 then Inr ()
    else Inl (STR  ''checks ---'' +
      STR '' all valid sols: '' + str_of_bool b1 +
      STR '', all distinct sols: '' + str_of_bool b2 +
      STR '', unsat check (< thresh sols): '' + str_of_bool b3)
  )"

definition BSAT ::"
  'fml \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> ('a \<Rightarrow> bool) list \<Rightarrow> String.literal + nat"
where "BSAT F S thresh xs = (
  case check_BSAT_sols F S thresh xs of
    Inl err \<Rightarrow> Inl err
  | Inr _ \<Rightarrow> Inr (length xs)
)"

(* A size certificate is simply a list of solutions*)
definition size_xorL_cert :: "
  'fml \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow>
  (nat \<Rightarrow> (bool list \<times> bool)) \<Rightarrow> nat \<Rightarrow>
  (('a \<Rightarrow> bool) list) \<Rightarrow> String.literal + nat"
  where "size_xorL_cert F S thresh xorsl i xs = (
    let xors = map (xor_from_bits S \<circ> xorsl) [0..<i]  in
    let Fenc = fold enc_xor xors F in
    BSAT Fenc S thresh xs
  )"

(* Checks whether the value of m is an appropriate value
  Especially in the case where 1 \<le> m \<le> |S|-1 *)
fun approxcore_xorsL_cert :: "
  'fml \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow>
  nat \<times> ('a \<Rightarrow> bool) list \<times> ('a \<Rightarrow> bool) list \<Rightarrow>
  (nat \<Rightarrow> (bool list \<times> bool))
  \<Rightarrow> String.literal + nat"
where "approxcore_xorsL_cert F S thresh (m,cert1,cert2) xorsl = (
  if 1 \<le> m \<and> m \<le> length S
  then
    case size_xorL_cert F S thresh xorsl (m-1) cert1 of
      Inl err \<Rightarrow> Inl (STR ''cert1 '' + err)
    | Inr n \<Rightarrow>
    if n \<ge> thresh
    then
      if m = length S
      then Inr (2 ^ length S)
      else
        case size_xorL_cert F S thresh xorsl m cert2 of
          Inl err \<Rightarrow> Inl (STR ''cert2 '' + err)
        | Inr c \<Rightarrow>
          if c < thresh then Inr (2 ^ m * c)
          else Inl (STR ''too many solutions at m added XORs'')
    else Inl (STR ''too few solutions at m-1 added XORs'')
  else
     Inl (STR ''invalid value of m, need 1 <= m <= |S|''))"

(* Compute the correct choice of n up to a bound arbitrarily set to 256 for now *)
definition find_t :: "real \<Rightarrow> nat"
where "find_t \<delta> = (
  case find (\<lambda>i. appmc.raw_median_bound 0.14 i < \<delta>) [0..<256] of
    Some m \<Rightarrow> m
  | None \<Rightarrow> appmc.fix_t \<delta>
  )"

fun fold_approxcore_xorsL_cert:: "
  'fml \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow>
  nat \<Rightarrow> nat \<Rightarrow>
  (nat \<Rightarrow> (nat \<times> ('a \<Rightarrow> bool) list \<times> ('a \<Rightarrow> bool) list)) \<Rightarrow>
  (nat \<Rightarrow> nat \<Rightarrow> (bool list \<times> bool))
  \<Rightarrow> String.literal + (nat list)"
  where
  "fold_approxcore_xorsL_cert F S thresh t 0 cs xorsLs = Inr []"
| "fold_approxcore_xorsL_cert F S thresh t (Suc i) cs xorsLs = (
    let it = t - Suc i in
    case approxcore_xorsL_cert F S thresh (cs it) (xorsLs it) of
      Inl err \<Rightarrow> Inl (STR ''round '' + str_of_nat it + STR '' '' + err)
    | Inr n \<Rightarrow>
      (case fold_approxcore_xorsL_cert F S thresh t i cs xorsLs of
          Inl err \<Rightarrow> Inl err
        | Inr ns \<Rightarrow> Inr (n # ns)))"

definition calc_median::"
  'fml \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
  (nat \<Rightarrow> (nat \<times> ('a \<Rightarrow> bool) list \<times> ('a \<Rightarrow> bool) list)) \<Rightarrow>
  (nat \<Rightarrow> nat \<Rightarrow> (bool list \<times> bool)) \<Rightarrow>
  String.literal + nat"
  where "calc_median F S thresh t ms xorsLs = (
      case fold_approxcore_xorsL_cert F S thresh t t ms xorsLs of
        Inl err \<Rightarrow> Inl err
      | Inr ls \<Rightarrow> Inr (sort ls ! (t div 2))
  )"

fun certcheck::"
  'fml \<Rightarrow> 'a list \<Rightarrow>
  real \<Rightarrow> real \<Rightarrow>
  (('a \<Rightarrow> bool) list \<times>
  (nat \<Rightarrow> (nat \<times> ('a \<Rightarrow> bool) list \<times> ('a \<Rightarrow> bool) list))) \<Rightarrow>
  (nat \<Rightarrow> nat \<Rightarrow> (bool list \<times> bool)) \<Rightarrow>
  String.literal + nat"
  where "certcheck F S \<epsilon> \<delta> (m0,ms) xorsLs = (
    let \<epsilon> = appmc.mk_eps \<epsilon> in
    let thresh = appmc.compute_thresh \<epsilon> in
    case BSAT F S thresh m0 of Inl err \<Rightarrow> Inl err
    | Inr Y \<Rightarrow>
    if Y < thresh then Inr Y
    else
      let t = find_t \<delta> in
      calc_median F S thresh t ms xorsLs)"

(* The correctness property for BSAT oracle calls that
   will be certified externally through proof logging *)
context
  assumes check_unsat: "\<And>F. check_unsat F \<Longrightarrow> sols F = {}"
begin

lemma sols_fold_ban_sol:
  shows"sols (fold ban_sol ls F) =
  sols F \<inter> {\<omega>. (\<forall>vs \<in> set ls. map \<omega> (map fst vs) \<noteq> map snd vs)}"
proof (induction ls arbitrary: F)
  case Nil
  then show ?case by auto
next
  case (Cons vs ls)
  show ?case
    using Cons(1) sols_ban_sol
    by auto
qed

lemma inter_cong_right:
  assumes "\<And>x. x \<in> A \<Longrightarrow> x \<in> B \<longleftrightarrow> x \<in> C"
  shows "A \<inter> B = A \<inter> C"
  using assms by auto

lemma proj_sol_canon_map_of:
  assumes "distinct S" "length S = length w"
  shows "proj_sol S (canon_map_of (zip S w)) = w"
  using assms
  unfolding proj_sol_def canon_map_of_def
proof (induction w arbitrary: S)
  case Nil
  then show ?case
    by auto
next
  case (Cons a w)
  obtain s ss where ss: "S = s # ss"
    by (metis Cons.prems(2) Suc_le_length_iff order.refl)
  then show ?case
    apply clarsimp
    by (smt (z3) Cons.IH Cons.prems(2) add.right_neutral add_Suc_right distinct.simps(2) list.size(4) local.Cons(2) map_eq_conv nat.inject)
qed

lemma proj_sol_cong:
  assumes "restr (set S) A = restr (set S) B"
  shows "proj_sol S A = proj_sol S B"
  using assms
  unfolding proj_sol_def restr_def map_eq_conv
  by (metis option.simps(1))

lemma canon_map_of_map_of:
  assumes "length S = length x"
  assumes "canon_map_of (zip S x) \<in> A"
  shows "map_of (zip S x) \<in> proj (set S) A"
proof -
  define f where "f = (\<lambda>xa. case map_of (zip S x) xa of
           None \<Rightarrow> False | Some b \<Rightarrow> b)"
  have "map_of (zip S x) =
       (\<lambda>y. if y \<in> set S then Some (f y) else None)"
    unfolding f_def fun_eq_iff
    using map_of_zip_is_Some[OF assms(1)]
    by (metis option.case_eq_if option.distinct(1) option.exhaust option.sel)
  thus ?thesis
  using assms unfolding canon_map_of_def ApproxMCCore.proj_def restr_def image_def
  using f_def by auto
qed

lemma proj_proj_sol_map_of_zip_1:
  assumes "distinct S" "length S = length w"
  assumes w: "w \<in> rdb"
  shows "
    map_of (zip S w) \<in>
    proj (set S) {\<omega>. proj_sol S \<omega> \<in> rdb}"
  apply (intro canon_map_of_map_of[OF assms(2)])
  using proj_sol_canon_map_of[OF assms(1-2)] w by auto

lemma proj_proj_sol_map_of_zip_2:
  assumes "\<And>bs. bs \<in> rdb \<Longrightarrow> length bs = length S"
  assumes w: "w \<in> proj (set S) {\<omega>. proj_sol S \<omega> \<in> rdb}"
  shows "
    w \<in> (map_of \<circ> zip S) ` rdb"
proof -
  obtain ww where ww: "proj_sol S ww \<in> rdb" "w = restr (set S) ww"
  using w unfolding ApproxMCCore.proj_def
  by auto

  have "w = map_of (zip S (proj_sol S ww))"
    unfolding ww restr_def proj_sol_def map_of_zip_map
    by auto

  thus ?thesis using ww
  by (auto simp add: image_def)
qed

lemma proj_proj_sol_map_of_zip:
  assumes "distinct S"
  assumes "\<And>bs. bs \<in> rdb \<Longrightarrow> length bs = length S"
  shows "
    proj (set S) {\<omega>. proj_sol S \<omega> \<in> rdb} =
    (map_of \<circ> zip S) ` rdb"
  apply (rule antisym)
  subgoal
    using proj_proj_sol_map_of_zip_2[OF assms(2)]
    by blast
  using assms(2)
  by (auto intro!: proj_proj_sol_map_of_zip_1[OF assms(1)])

definition ban_proj_sol ::"'a list \<Rightarrow> ('a \<Rightarrow> bool) list \<Rightarrow> 'fml \<Rightarrow> 'fml"
where "ban_proj_sol S xs F =
    fold ban_sol (map (zip S \<circ> proj_sol S) xs) F"

lemma check_sol_imp_proj:
  assumes "w \<in> sols F"
  shows "map_of (zip S (proj_sol S w)) \<in> proj (set S) (sols F)"
  unfolding proj_sol_def map_of_zip_map ApproxMCCore.proj_def image_def restr_def
  using assms by auto

lemma checked_BSAT_lower:
  assumes S: "distinct S"
  assumes "check_BSAT_sols F S thresh xs = Inr ()"
  shows "length xs \<le> card (proj (set S) (sols F))"
  "length xs < thresh \<Longrightarrow>
    card (proj (set S) (sols F)) = length xs"
proof -
  define Sxs where "Sxs = map (proj_sol S) xs"
  have dSxs: "distinct Sxs"
    using assms unfolding Sxs_def check_BSAT_sols_def Let_def
    by (auto split: if_splits)

  have lSxs: "\<And>x. x \<in> set Sxs \<Longrightarrow> length x = length S"
    unfolding Sxs_def proj_sol_def by auto
  define SSxs where "SSxs = map (zip S) Sxs"
  have dSSxs: "distinct (map map_of SSxs)"
    unfolding SSxs_def
    using dSxs unfolding inj_on_def distinct_map
    by (smt (verit) assms(1) imageE lSxs list.set_map map_of_zip_inject)

  have *: "set (map map_of SSxs) \<subseteq> proj (set S) (sols F)"
    unfolding Sxs_def SSxs_def
    using assms unfolding check_BSAT_sols_def Let_def
    by (auto intro!: check_sol_imp_proj split: if_splits simp add: check_sol list_all_iff)
  have "length xs = card (set (map map_of SSxs))"
    by (metis SSxs_def Sxs_def dSSxs length_map length_remdups_card_conv remdups_id_iff_distinct)

  thus "length xs \<le> card (proj (set S) (sols F))"
    by (metis * List.finite_set card_mono card_proj(1))

  have frr1: "(\<forall>vs \<in> set SSxs. map \<omega> (map fst vs) \<noteq> map snd vs) \<Longrightarrow>
    (\<forall>vs \<in> set Sxs. proj_sol S \<omega> \<noteq> vs)" for \<omega>
    apply (clarsimp simp add: proj_sol_def SSxs_def)
    by (metis (mono_tags, lifting) in_set_zip nth_map)
  have frr2: "(\<forall>vs \<in> set Sxs. proj_sol S \<omega> \<noteq> vs) \<Longrightarrow>
    (vs \<in> set SSxs \<Longrightarrow> map \<omega> (map fst vs) \<noteq> map snd vs)" for vs \<omega>
    apply (clarsimp simp add: proj_sol_def SSxs_def)
    by (smt (z3) Sxs_def assms(1) length_map length_map length_map map_eq_conv map_fst_zip map_of_zip_inject mem_Collect_eq nth_map nth_map nth_map proj_sol_def set_conv_nth set_conv_nth zip_map_fst_snd)

  have frr: "{\<omega>. (\<forall>vs \<in> set SSxs. map \<omega> (map fst vs) \<noteq> map snd vs)} =
    {\<omega>. (\<forall>vs \<in> set Sxs. proj_sol S \<omega> \<noteq> vs)}"
    using frr1 frr2 by auto

  moreover {
    assume "length xs < thresh"
    then have "sols (ban_proj_sol S xs F) = {}"
      apply (intro check_unsat)
      using assms(2) unfolding check_BSAT_sols_def Let_def
      by (auto simp add:ban_proj_sol_def o_assoc split: if_splits)

    then have "sols F \<inter> {\<omega>. (\<forall>vs \<in> set Sxs. proj_sol S \<omega> \<noteq> vs)} = {}"
      unfolding ban_proj_sol_def sols_fold_ban_sol
      frr[symmetric]
      by (auto simp add: SSxs_def Sxs_def)
    then have 1:"proj (set S) (sols F) \<inter>
      proj (set S)
       {\<omega>. \<forall>vs\<in>set Sxs. proj_sol S \<omega> \<noteq> vs} = {}"
      unfolding ApproxMCCore.proj_def
      using proj_sol_cong
      by (smt (verit, del_insts) disjoint_iff_not_equal image_iff mem_Collect_eq)

    have 2: "proj (set S) (sols F) \<inter> -proj (set S) {\<omega>. (\<forall>vs \<in> set Sxs. proj_sol S \<omega> \<noteq> vs)} =
      proj (set S) (sols F) \<inter> proj (set S)  {\<omega>. proj_sol S \<omega> \<in> set Sxs}"
      apply (intro inter_cong_right)
      by (auto intro!: proj_sol_cong simp add: ApproxMCCore.proj_def ) 
      
    have 3: "proj (set S)  {\<omega>. proj_sol S \<omega> \<in> set Sxs} = (map_of \<circ> zip S) ` (set Sxs)"
      apply (intro proj_proj_sol_map_of_zip[OF S])
      using lSxs by auto

    have 4: " proj (set S) (sols F) \<inter> (map_of \<circ> zip S) ` (set Sxs) =
      (map_of \<circ> zip S) ` (set Sxs)"
      using "*" SSxs_def by auto

    have **:"proj (set S) (sols F) =
      proj (set S) (sols F) \<inter> proj (set S) {\<omega>. (\<forall>vs \<in> set Sxs. proj_sol S \<omega> \<noteq> vs)} \<union>
      proj (set S) (sols F) \<inter> -proj (set S) {\<omega>. (\<forall>vs \<in> set Sxs. proj_sol S \<omega> \<noteq> vs)}"
      by auto

    have "card (proj (set S) (sols F)) =
      card ((map_of \<circ> zip S) ` (set Sxs))"
      apply (subst **)
      apply (subst card_Un_disjoint)
      using 1 2 3 4 by (auto simp add: card_proj(1))

    then have "card (proj (set S) (sols F)) = length xs"
      by (simp add: SSxs_def \<open>length xs = card (set (map map_of SSxs))\<close>)
  }
  thus "length xs < thresh \<Longrightarrow> card (proj (set S) (sols F)) = length xs"
  by auto
qed

lemma good_BSAT:
  assumes "distinct S"
  assumes "BSAT F S thresh xs = Inr n"
  shows "n \<le> card (proj (set S) (sols F))"
    "n < thresh \<Longrightarrow>
      card (proj (set S) (sols F)) = n"
  using checked_BSAT_lower[OF assms(1)] assms(2)
  by (auto simp add: BSAT_def split: if_splits sum.splits)

lemma size_xorL_cert:
  assumes "distinct S"
  assumes "size_xorL_cert F S thresh xorsl i xs = Inr n"
  shows
    "size_xorL F S xorsl i \<ge> n"
    "n < thresh \<longrightarrow> size_xorL F S xorsl i = n"
  using assms unfolding size_xorL_def size_xorL_cert_def
  using good_BSAT by auto

lemma approxcore_xorsL_cert:
  assumes S: "distinct S"
  assumes "approxcore_xorsL_cert F S thresh mc xorsl = Inr n"
  shows "approxcore_xorsL F S thresh xorsl = n"
proof -
  obtain m cert1 cert2 where mc: "mc = (m,cert1,cert2)"
    using prod_cases3 by blast
  obtain nn1 where
    nn1:"size_xorL_cert F S thresh xorsl (m-1) cert1 = Inr nn1"
    using assms unfolding mc
    by (auto split: if_splits sum.splits)

  from  size_xorL_cert[OF S this]
  have nn1l:
    "nn1 \<le> size_xorL F S xorsl (m - 1)"
    "nn1 < thresh \<longrightarrow> size_xorL F S xorsl (m - 1) = nn1" by auto

  have m: "1 \<le> m" "m \<le> length S"
    "nn1 \<ge> thresh" and
    ms: "m = length S \<and> n = 2 ^ length S \<or>
      m < length S"
    using nn1 assms unfolding mc
    by (auto split: if_splits simp add: Let_def)

  have bnd: "\<And>i. 1 \<le> i \<Longrightarrow> i \<le> m -1 \<Longrightarrow>
      size_xorL F S xorsl i \<ge> thresh"
    using nn1l m(3)
    by (meson assms(1) dual_order.trans size_xorL_anti_mono)

  note ms
  moreover {
    assume *: "m = length S"
    then have "find (check_xorL F S thresh xorsl) [1..<length S] = None"
      unfolding find_None_iff check_xorL_def
      by (auto simp add: bnd leD)
    then have ?thesis
      unfolding approxcore_xorsL_def
      using * ms by force
  }
  moreover {
    assume *: "m < length S"

    obtain nn2 where
      nn2:"size_xorL_cert F S thresh xorsl m cert2 = Inr nn2"
        "nn2 < thresh"
        "n = 2 ^ m * nn2"
      using assms * unfolding mc
      by (auto split: if_splits sum.splits)

    from size_xorL_cert[OF S nn2(1)]
    have nn2l:
      "size_xorL F S xorsl m = nn2"
      using nn2(2) by blast

    then have "find (check_xorL F S thresh xorsl) [Suc 0..<length S] = Some m"
      apply (intro find_upto_SomeI)
      subgoal by (auto  simp add: m * bnd check_xorL_def leD)
      subgoal 
        using "*" calculation(1) size_xorL_cert(2) nn2
        by (auto  simp add: m * bnd check_xorL_def leD) 
      subgoal using m(1) by linarith
      by (auto  simp add: m * bnd check_xorL_def leD)

    then have ?thesis
      unfolding approxcore_xorsL_def using nn2 nn2l
      by auto
  }
  ultimately show ?thesis by auto
qed

lemma fold_approxcore_xorsL_cert:
  assumes S: "distinct S"
  assumes "i \<le> t"
  assumes "fold_approxcore_xorsL_cert F S thresh t i cs xorsLs = Inr ns"
  shows "map (approxcore_xorsL F S thresh \<circ> xorsLs) [t-i..<t] = ns "
  using assms(2-3)
proof (induction i arbitrary: ns)
  case 0
  then show ?case
    by auto
next
  case c:(Suc i)
  from c(3)
  obtain n nss where *:"ns = n # nss"
     "fold_approxcore_xorsL_cert F S thresh t i cs xorsLs = Inr nss"
     "approxcore_xorsL_cert F S thresh (cs (t-Suc i)) (xorsLs (t-Suc i)) = Inr n"
    by (auto simp add: Let_def split: sum.splits)

  have "i \<le> t" using c by auto
  from c(1)[OF this *(2)]
  have 2: "nss =
    map (approxcore_xorsL F S thresh \<circ> xorsLs) [t - i..<t]"
    by auto

  have i:"[t - Suc i..<t] = (t - Suc i) # [t - i..<t]"
    apply (subst upt_rec)
    using c(2)
    using Suc_diff_Suc Suc_le_lessD by presburger

  show ?case
    unfolding i *
    apply (clarsimp simp add: 2 )
    using  2 "*"(3) approxcore_xorsL_cert assms(1) by blast
qed

lemma calc_median:
  assumes S: "distinct S"
  assumes "calc_median F S thresh t ms xorsLs = Inr n"
  shows "median t (approxcore_xorsL F S thresh \<circ> xorsLs) = n"
  using assms
  unfolding calc_median_def  median_def
  apply (clarsimp simp add: assms split: if_splits sum.splits)
  using  fold_approxcore_xorsL_cert[OF S]
  by (metis diff_is_0_eq' dual_order.refl)

lemma compute_t_find_t[simp]:
  shows "appmc.compute_t \<delta> (find_t \<delta>) = find_t \<delta>"
  unfolding find_t_def appmc.compute_t_def
  apply (clarsimp simp add: option.case_eq_if)
  unfolding find_Some_iff
  by auto

lemma certcheck:
  assumes "distinct S"
  assumes "certcheck F S \<epsilon> \<delta> (m0,ms) xorsLs = Inr n"
  shows "approxmc_mapL F S \<epsilon> \<delta> (find_t \<delta>) xorsLs = n"
  using assms(2)
  unfolding approxmc_mapL_def
  using good_BSAT apply (clarsimp split: sum.splits if_splits simp add: Let_def)
  subgoal using order_le_less_trans assms by blast
  using assms order.strict_trans1
  by (meson assms(1) calc_median)

lemma certcheck':
  assumes "distinct S"
  assumes "\<not>isl (certcheck F S \<epsilon> \<delta> m xorsLs)"
  shows "projr (certcheck F S \<epsilon> \<delta> m xorsLs) =
    approxmc_mapL F S \<epsilon> \<delta> (find_t \<delta>) xorsLs"
  by (metis certcheck assms(1) assms(2) sum.collapse(2) surj_pair)

(* For any function f mapping randomness to certificates,
  The probability that the certificate accepts (\<not>isl)
  With output c not in the interval is at most \<delta> *)
lemma certcheck_sound:
  assumes \<delta>: "\<delta> > 0" "\<delta> < 1"
  assumes \<epsilon>: "\<epsilon> > 0"
  assumes S: "distinct S"
  shows "
    measure_pmf.prob
      (map_pmf (\<lambda>r. certcheck F S \<epsilon> \<delta> (f r) r)
        (random_seed_xors (find_t \<delta>) (length S)))
      {c. \<not>isl c \<and>
        real (projr c) \<notin>
        {real (card (proj (set S) (sols F))) / (1 + \<epsilon>)..
          (1 + \<epsilon>) * real (card (proj (set S) (sols F)))}} \<le> \<delta>"
proof -
  have "measure_pmf.prob
      (map_pmf (\<lambda>r. certcheck F S \<epsilon> \<delta> (f r) r)
        (random_seed_xors (find_t \<delta>) (length S)))
      {c. \<not>isl c \<and>
        real (projr c) \<notin>
        {real (card (proj (set S) (sols F))) / (1 + \<epsilon>)..
          (1 + \<epsilon>) * real (card (proj (set S) (sols F)))}} \<le>
   prob_space.prob
      (map_pmf (approxmc_mapL F S \<epsilon> \<delta> (find_t \<delta>))
        (random_seed_xors (appmc.compute_t \<delta> (find_t \<delta>)) (length S)))
      {c. real c \<notin>
        {real (card (proj (set S) (sols F))) / (1 + \<epsilon>)..
          (1 + \<epsilon>) * real (card (proj (set S) (sols F)))}}"
    unfolding measure_map_pmf compute_t_find_t
    by (auto intro!: measure_pmf.finite_measure_mono simp add: certcheck'[OF S])
  also have "... \<le> \<delta>"
    by (intro approxmcL_sound'[OF assms])
  finally show ?thesis by auto
qed

(* A completeness theorem for the checker in the face of probabilistic guarantees
  It is stated with a "promise"-style guarantee:
  For any function f mapping randomness to certificates,
  If the checker accepts (\<not>isl) the output of f on any randomness
  Then the output c is in the interval with high probability (1 - \<delta>) *)
lemma certcheck_promise_complete:
  assumes \<delta>: "\<delta> > 0" "\<delta> < 1"
  assumes \<epsilon>: "\<epsilon> > 0"
  assumes S: "distinct S"
  assumes r: "\<And>r.
    r \<in> set_pmf (random_seed_xors (find_t \<delta>) (length S)) \<Longrightarrow>
    \<not>isl (certcheck F S \<epsilon> \<delta> (f r) r)"
  shows "
    measure_pmf.prob
      (map_pmf (\<lambda>r. certcheck F S \<epsilon> \<delta> (f r) r)
        (random_seed_xors (find_t \<delta>) (length S)))
      {c. real (projr c) \<in>
        {real (card (proj (set S) (sols F))) / (1 + \<epsilon>)..
          (1 + \<epsilon>) * real (card (proj (set S) (sols F)))}} \<ge> 1 - \<delta>"
proof -
  have "
   measure_pmf.prob
      (map_pmf (\<lambda>r. certcheck F S \<epsilon> \<delta> (f r) r)
        (random_seed_xors (find_t \<delta>) (length S)))
      {c. real (projr c) \<in>
        {real (card (proj (set S) (sols F))) / (1 + \<epsilon>)..
          (1 + \<epsilon>) * real (card (proj (set S) (sols F)))}} =
   measure_pmf.prob
      (map_pmf (approxmc_mapL F S \<epsilon> \<delta> (find_t \<delta>))
        (random_seed_xors (appmc.compute_t \<delta> (find_t \<delta>)) (length S)))
      {c. real c \<in>
        {real (card (proj (set S) (sols F))) / (1 + \<epsilon>)..
          (1 + \<epsilon>) * real (card (proj (set S) (sols F)))}}"
    unfolding measure_map_pmf compute_t_find_t
    by (auto intro!: measure_pmf.measure_pmf_eq simp add: certcheck'[OF S] r)
  also have "... \<ge> 1 -  \<delta>"
    by (intro approxmcL_sound[OF assms(1-4)])
  finally show ?thesis by auto
qed

end

lemma certcheck_code[code]:
   "certcheck F S \<epsilon> \<delta> (m0,ms) xorsLs = (
    if \<delta> > 0 \<and> \<delta> < 1 \<and> \<epsilon> > 0 \<and> distinct S then
      (let \<epsilon> = appmc.mk_eps \<epsilon> in
      let thresh = appmc.compute_thresh \<epsilon> in
      case BSAT F S thresh m0 of Inl err \<Rightarrow> Inl err
      | Inr Y \<Rightarrow>
      if Y < thresh then Inr Y
      else
        let t = find_t \<delta> in
        calc_median F S thresh t ms xorsLs)
     else Code.abort (STR ''invalid inputs'')
        (\<lambda>_. certcheck F S \<epsilon> \<delta> (m0,ms) xorsLs))"
  by auto

end

end

end
