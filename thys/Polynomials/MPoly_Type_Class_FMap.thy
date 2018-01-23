(* Author: Fabian Immler, Alexander Maletzky *)

section \<open>Executable Representation of Polynomial Mappings as Association Lists\<close>

theory MPoly_Type_Class_FMap
  imports
    MPoly_Type_Class
    Poly_Mapping_Finite_Map
begin

text \<open>In this theory, (type class) multivariate polynomials of type
  @{typ "('a, 'b) poly_mapping"} are represented as association lists.\<close>

text \<open>In principle, one could also build upon theory \<open>Polynomials\<close>, although there the representations of
  power-products and polynomials additionally have to satisfy certain invariants, which we do not
  require here.\<close>

lemma fmlookup_default_fmmap:
  "fmlookup_default d (fmmap f M) x = (if x \<in> fmdom' M then f (fmlookup_default d M x) else d)"
  by (auto simp: fmlookup_default_def fmdom'_notI split: option.splits)

lemma fmlookup_default_fmmap_keys: "fmlookup_default d (fmmap_keys f M) x =
  (if x \<in> fmdom' M then f x (fmlookup_default d M x) else d)"
  by (auto simp: fmlookup_default_def fmdom'_notI split: option.splits)

lemma compute_lcs_pp[code]:
  "lcs (Pm_fmap xs) (Pm_fmap ys) =
  Pm_fmap (fmmap_keys (\<lambda>k v. Orderings.max (lookup0 xs k) (lookup0 ys k)) (xs ++\<^sub>f ys))"
  by (rule poly_mapping_eqI)
    (auto simp add: fmlookup_default_fmmap_keys fmlookup_dom_iff fmdom'_notI
      lcs_poly_mapping.rep_eq fmdom'_notD)

lemma compute_deg_pp[code]:
  "deg_pm (Pm_fmap xs) = sum (the o fmlookup xs) (fmdom' xs)"
proof -
  have "deg_pm (Pm_fmap xs) = sum (lookup (Pm_fmap xs)) (keys (Pm_fmap xs))"
    by (rule deg_pm_superset) auto
  also have "\<dots> = sum (the o fmlookup xs) (fmdom' xs)"
    by (rule sum.mono_neutral_cong_left)
      (auto simp: fmlookup_dom'_iff fmdom'I in_keys_iff fmlookup_default_def fmdom'.rep_eq
        split: option.splits)
  finally show ?thesis .
qed

definition adds_pp_add_linorder::"('b \<Rightarrow>\<^sub>0 'a::add_linorder) \<Rightarrow> _ \<Rightarrow> bool"
  where [code_abbrev]: "adds_pp_add_linorder = (adds)"

lemma compute_adds_pp[code]:
  "adds_pp_add_linorder (Pm_fmap xs) (Pm_fmap ys) =
    (fmpred (\<lambda>k v. lookup0 xs k \<le> lookup0 ys k) (xs ++\<^sub>f ys))"
  for xs ys::"('a, 'b::add_linorder_min) fmap"
  unfolding adds_pp_add_linorder_def
  unfolding adds_poly_mapping
  using fmdom_notI
  by (force simp: fmlookup_dom_iff le_fun_def
      split: option.splits if_splits)


text\<open>Computing @{term lex} as below is certainly not the most efficient way, but it works.\<close>

lemma lex_pm_iff: "lex_pm s t = (\<forall>x. lookup s x \<le> lookup t x \<or> (\<exists>y<x. lookup s y \<noteq> lookup t y))"
  by (simp only: lex_pm.rep_eq lex_fun_def poly_mapping_eq_iff)

lemma compute_lex_pp[code]:
  "(lex_pm (Pm_fmap xs) (Pm_fmap (ys::('a::wellorder, 'b::ordered_comm_monoid_add) fmap))) =
    (let zs = xs ++\<^sub>f ys in
      fmpred (\<lambda>x v.
        lookup0 xs x \<le> lookup0 ys x \<or>
        \<not> fmpred (\<lambda>y w. y \<ge> x \<or> lookup0 xs y = lookup0 ys y) zs) zs
    )"
  unfolding Let_def lex_pm_iff fmpred_iff Pm_fmap.rep_eq fmlookup_add fmlookup_dom_iff
  apply (intro iffI)
   apply (metis fmdom'_notD fmlookup_default_if(2) fmlookup_dom'_iff leD)
  apply (metis eq_iff not_le fmdom'_notD fmlookup_default_if(2) fmlookup_dom'_iff)
  done

lemma compute_dord_pp[code]:
  "(dord_pm ord (Pm_fmap xs) (Pm_fmap (ys::('a::wellorder , 'b::ordered_comm_monoid_add) fmap))) =
    (let dx = deg_pm (Pm_fmap xs) in let dy = deg_pm (Pm_fmap ys) in
      dx < dy \<or> (dx = dy \<and> ord (Pm_fmap xs) (Pm_fmap ys))
    )"
  by (auto simp: Let_def deg_pm.rep_eq dord_fun_def dord_pm.rep_eq)
    (simp_all add: Pm_fmap.abs_eq)

subsubsection \<open>Computations\<close>

text \<open>Indeterminates are most conveniently represented by natural numbers:\<close>

abbreviation "X \<equiv> 0::nat"
abbreviation "Y \<equiv> 1::nat"
abbreviation "Z \<equiv> 2::nat"

definition "PM xs = Pm_fmap (fmap_of_list xs)" \<comment>\<open>sparse representation\<close>
definition "PM' xs = Pm_fmap (fmap_of_list (zip [0..<length xs] xs))" \<comment>\<open>dense representation\<close>

lemma
  "PM [(X, 2::nat), (Z, 7)] + PM [(Y, 3), (Z, 2)] = PM [(X, 2), (Z, 9), (Y, 3)]"
  "PM' [2, 0, 7::nat] + PM' [0, 3, 2] = PM' [2, 3, 9]"
  by eval+

lemma
  "PM [(X, 2::nat), (Z, 7)] - PM [(X, 2), (Z, 2)] = PM [(Z, 5)]"
  by eval

lemma
  "lcs (PM [(X, 2::nat), (Y, 1), (Z, 7)]) (PM [(Y, 3), (Z, 2)]) = PM [(X, 2), (Y, 3), (Z, 7)]"
  by eval

lemma
  "(PM [(X, 2::nat), (Z, 1)]) adds (PM [(X, 3), (Y, 2), (Z, 1)])"
  by eval

lemma
  "lookup (PM [(X, 2::nat), (Z, 3)]) X = 2"
  by eval

lemma
  "deg_pm (PM [(X, 2::nat), (Y, 1), (Z, 3), (X, 1)]) = 6"
  by eval

lemma
  "lex_pm (PM [(X, 2::nat), (Y, 1), (Z, 3)]) (PM [(X, 4)])"
by eval

lemma
  "lex_pm (PM [(X, 2::nat), (Y, 1), (Z, 3)]) (PM [(X, 4)])"
  by eval

lemma
  "\<not> (dlex_pm (PM [(X, 2::nat), (Y, 1), (Z, 3)]) (PM [(X, 4)]))"
  by eval

lemma
  "dlex_pm (PM [(X, 2::nat), (Y, 1), (Z, 2)]) (PM [(X, 5)])"
  by eval

lemma
  "\<not> (drlex_pm (PM [(X, 2::nat), (Y, 1), (Z, 2)]) (PM [(X, 5)]))"
  by eval

subsection \<open>Implementation of Multivariate Polynomials as Association Lists\<close>

subsubsection \<open>Unordered Power-Products\<close>

context includes fmap.lifting begin
lift_definition shift_keys::"'a::comm_powerprod \<Rightarrow> ('a, 'b) fmap \<Rightarrow> ('a, 'b) fmap"
  is "\<lambda>t m x. if t adds x then m (x - t) else None"
proof -
  fix a and f::"'a \<Rightarrow> 'b option"
  assume "finite (dom f)"
  have "dom (\<lambda>x. if a adds x then f (x - a) else None) \<subseteq> (+) a ` dom f"
    by (auto simp: adds_def domI split: if_splits)
  also have "finite \<dots>"
    using \<open>finite (dom f)\<close> by simp
  finally (finite_subset) show "finite (dom (\<lambda>x. if a adds x then f (x - a) else None))" .
qed

definition "shift_map_keys t f m = fmmap f (shift_keys t m)"

lemma compute_shift_map_keys[code]:
  "shift_map_keys t f (fmap_of_list xs) = fmap_of_list (map (\<lambda>(k, v). (t + k, f v)) xs)"
  unfolding shift_map_keys_def
  apply transfer
  subgoal for f t xs
  proof -
    show ?thesis
      apply (rule ext)
      subgoal for x
        apply (cases "t adds x")
        subgoal by (induction xs) (auto simp: adds_def )
        subgoal by (induction xs) (auto simp: adds_def )
        done
      done
  qed
  done

end

lemmas [simp] = compute_zero_pp[symmetric]

lemma compute_monom_mult_poly_mapping[code]:
  "monom_mult c t (Pm_fmap xs) = Pm_fmap (if c = 0 then fmempty else shift_map_keys t (( * ) c) xs)"
proof (cases "c = 0")
  case True
  hence "monom_mult c t (Pm_fmap xs) = 0" using monom_mult_left0 by simp
  thus ?thesis using True
    by simp
next
  case False
  thus ?thesis
    by (auto simp: simp: fmlookup_default_def shift_map_keys_def monom_mult.rep_eq
        adds_def group_eq_aux shift_keys.rep_eq
        intro!: poly_mapping_eqI split: option.splits)
qed

lemma compute_monomial[code]:
  "monomial c t = (if c = 0 then 0 else PM [(t, c)])"
  by (auto intro!: poly_mapping_eqI simp: PM_def fmlookup_default_def lookup_single)

lemma compute_mult_poly_mapping[code]:
  "Pm_fmap (fmap_of_list xs) * q = (case xs of ((t, c) # ys) \<Rightarrow>
    (monom_mult c t q + except (Pm_fmap (fmap_of_list ys)) {t} * q) | _ \<Rightarrow>
    Pm_fmap fmempty)"
proof (split list.splits, simp, intro conjI impI allI, goal_cases)
  case (1 t c ys)
  have "Pm_fmap (fmupd t c (fmap_of_list ys)) = PM [(t, c)] + except (PM ys) {t}"
    by (auto simp: PM_def fmlookup_default_def lookup_add lookup_except
        split: option.splits intro!: poly_mapping_eqI)
  also have "PM [(t, c)] = monomial c t"
    by (auto simp: PM_def lookup_single fmlookup_default_def intro!: poly_mapping_eqI)
  finally show ?case
    by (simp add: algebra_simps times_monomial_left PM_def)
qed

lemma compute_except_poly_mapping[code]:
  "except (Pm_fmap xs) S = Pm_fmap (fmfilter (\<lambda>k. k \<notin> S) xs)"
  by (auto simp: fmlookup_default_def lookup_except split: option.splits intro!: poly_mapping_eqI)


subsubsection \<open>Computations\<close>

abbreviation "MP \<equiv> PM"
abbreviation "MP' \<equiv> PM'"


lemma
  "keys (MP [(PM [(X, 2::nat), (Z, 3)], 1::rat), (PM [(Y, 3), (Z, 2)], 2), (PM [(X, 1), (Y, 1)], 0)]) =
    {PM [(X, 2), (Z, 3)], PM [(Y, 3), (Z, 2)]}"
  by eval

lemma
  "- MP [(PM [(X, 2::nat), (Z, 7)], 1::rat), (PM [(Y, 3), (Z, 2)], 2)] =
    MP [(PM [(X, 2), (Z, 7)], - 1), (PM [(Y, 3), (Z, 2)], - 2)]"
by eval

lemma
  "MP [(PM [(X, 2::nat), (Z, 7)], 1::rat), (PM [(Y, 3), (Z, 2)], 2)] + MP [(PM [(X, 2), (Z, 4)], 1), (PM [(Y, 3), (Z, 2)], -2)] =
    MP [(PM [(X, 2), (Z, 7)], 1), (PM [(X, 2), (Z, 4)], 1)]"
by eval

lemma
  "MP [(PM [(X, 2::nat), (Z, 7)], 1::rat), (PM [(Y, 3), (Z, 2)], 2)] - MP [(PM [(X, 2), (Z, 4)], 1), (PM [(Y, 3), (Z, 2)], -2)] =
    MP [(PM [(X, 2), (Z, 7)], 1), (PM [(Y, 3), (Z, 2)], 4), (PM [(X, 2), (Z, 4)], - 1)]"
by eval

lemma
  "lookup (MP [(PM [(X, 2::nat), (Z, 7)], 1::rat), (PM [(Y, 3), (Z, 2)], 2), (PM [], 2)]) (PM [(X, 2), (Z, 7)]) = 1"
by eval

lemma
  "MP [(PM [(X, 2::nat), (Z, 7)], 1::rat), (PM [(Y, 3), (Z, 2)], 2)] \<noteq> MP [(PM [(X, 2), (Z, 4)], 1), (PM [(Y, 3), (Z, 2)], -2)]"
by eval

lemma
  "MP [(PM [(X, 2::nat), (Z, 7)], 0::rat), (PM [(Y, 3), (Z, 2)], 0)] = 0"
by eval

lemma
  "monom_mult (3::rat) (PM [(Y, 2::nat)]) (MP [(PM [(X, 2), (Z, 1)], 1), (PM [(Y, 3), (Z, 2)], 2)]) =
    MP [(PM [(Y, 2), (Z, 1), (X, 2)], 3), (PM [(Y, 5), (Z, 2)], 6)]"
by eval

lemma
  "monomial (-4::rat) (PM [(X, 2::nat)]) = MP [(PM [(X, 2)], - 4)]"
by eval

lemma
  "monomial (0::rat) (PM [(X, 2::nat)]) = 0"
by eval

lemma
  "MP [(PM [(X, 2::nat), (Z, 1)], 1::rat), (PM [(Y, 3), (Z, 2)], 2)] *
      MP [(PM [(X, 2), (Z, 3)], 1), (PM [(Y, 3), (Z, 2)], -2)] =
    MP [(PM [(X, 4), (Z, 4)], 1), (PM [(X, 2), (Z, 3), (Y, 3)], - 2), (PM [(Y, 6), (Z, 4)], - 4), (PM [(Y, 3), (Z, 5), (X, 2)], 2)]"
  by eval

subsubsection \<open>Ordered Power-Products\<close>

lemma foldl_assoc:
  assumes "\<And>x y z. f (f x y) z = f x (f y z)"
  shows "foldl f (f a b) xs = f a (foldl f b xs)"
proof (induct xs arbitrary: a b)
  fix a b
  show "foldl f (f a b) [] = f a (foldl f b [])" by simp
next
  fix a b x xs
  assume "\<And>a b. foldl f (f a b) xs = f a (foldl f b xs)"
  from assms[of a b x] this[of a "f b x"]
    show "foldl f (f a b) (x # xs) = f a (foldl f b (x # xs))" unfolding foldl_Cons by simp
qed

context ordered_powerprod
begin

definition list_max::"'a list \<Rightarrow> 'a" where
  "list_max xs \<equiv> foldl ordered_powerprod_lin.max 0 xs"

lemma list_max_Cons:
  shows "list_max (x # xs) = ordered_powerprod_lin.max x (list_max xs)"
unfolding list_max_def foldl_Cons
proof -
  have "foldl ordered_powerprod_lin.max (ordered_powerprod_lin.max x 0) xs =
          ordered_powerprod_lin.max x (foldl ordered_powerprod_lin.max 0 xs)"
    by (rule foldl_assoc, rule ordered_powerprod_lin.max.assoc)
  from this ordered_powerprod_lin.max.commute[of 0 x]
    show "foldl ordered_powerprod_lin.max (ordered_powerprod_lin.max 0 x) xs =
            ordered_powerprod_lin.max x (foldl ordered_powerprod_lin.max 0 xs)" by simp
qed

lemma list_max_empty:
  shows "list_max [] = 0"
unfolding list_max_def by simp

lemma list_max_in_list:
  fixes xs::"'a list"
  assumes "xs \<noteq> []"
  shows "list_max xs \<in> set xs"
using assms
proof (induct xs, simp)
  fix x xs
  assume IH: "xs \<noteq> [] \<Longrightarrow> list_max xs \<in> set xs"
  show "list_max (x # xs) \<in> set (x # xs)"
  proof (cases "xs = []")
    case True
    hence "list_max (x # xs) = ordered_powerprod_lin.max 0 x" unfolding list_max_def by simp
    also have "\<dots> = x" unfolding ordered_powerprod_lin.max_def by (simp add: zero_min)
    finally show ?thesis by simp
  next
    assume "xs \<noteq> []"
    show ?thesis
    proof (cases "x \<preceq> list_max xs")
      case True
      hence "list_max (x # xs) = list_max xs"
        unfolding list_max_Cons ordered_powerprod_lin.max_def by simp
      thus ?thesis using IH[OF \<open>xs \<noteq> []\<close>] by simp
    next
      case False
      hence "list_max (x # xs) = x" unfolding list_max_Cons ordered_powerprod_lin.max_def by simp
      thus ?thesis by simp
    qed
  qed
qed

lemma list_max_maximum:
  fixes xs::"'a list"
  assumes "a \<in> set xs"
  shows "a \<preceq> (list_max xs)"
using assms
proof (induct xs)
  assume "a \<in> set []"
  thus "a \<preceq> list_max []" by simp
next
  fix x xs
  assume IH: "a \<in> set xs \<Longrightarrow> a \<preceq> list_max xs" and a_in: "a \<in> set (x # xs)"
  from a_in have "a = x \<or> a \<in> set xs" by simp
  thus "a \<preceq> list_max (x # xs)" unfolding list_max_Cons
  proof
    assume "a = x"
    thus "a \<preceq> ordered_powerprod_lin.max x (list_max xs)" by simp
  next
    assume "a \<in> set xs"
    from IH[OF this] show "a \<preceq> ordered_powerprod_lin.max x (list_max xs)"
      by (simp add: ordered_powerprod_lin.le_max_iff_disj)
  qed
qed

lemma list_max_nonempty:
  fixes xs::"'a list"
  assumes "xs \<noteq> []"
  shows "list_max xs = ordered_powerprod_lin.Max (set xs)"
proof -
  have fin: "finite (set xs)" by simp
  have "ordered_powerprod_lin.Max (set xs) = list_max xs"
  proof (rule ordered_powerprod_lin.Max_eqI[OF fin, of "list_max xs"])
    fix y
    assume "y \<in> set xs"
    from list_max_maximum[OF this] show "y \<preceq> list_max xs" .
  next
    from list_max_in_list[OF assms] show "list_max xs \<in> set xs" .
  qed
  thus ?thesis by simp
qed

lemma in_set_clearjunk_iff_map_of_eq_Some:
  "(a, b) \<in> set (AList.clearjunk xs) \<longleftrightarrow> map_of xs a = Some b"
  by (metis Some_eq_map_of_iff distinct_clearjunk map_of_clearjunk)

lemma Pm_fmap_of_list_eq_zero_iff:
  "Pm_fmap (fmap_of_list xs) = 0 \<longleftrightarrow> [(k, v)\<leftarrow>AList.clearjunk xs . v \<noteq> 0] = []"
  by (auto simp: poly_mapping_eq_iff fmlookup_default_def fun_eq_iff 
    in_set_clearjunk_iff_map_of_eq_Some filter_empty_conv fmlookup_of_list split: option.splits)

lemma fmdom'_clearjunk0: "fmdom' (clearjunk0 xs) = fmdom' xs - {x. fmlookup xs x = Some 0}"
  by (metis (no_types, lifting) clearjunk0_def fmdom'_drop_set fmfilter_alt_defs(2) fmfilter_cong' mem_Collect_eq)

lemma compute_lp_poly_mapping[code]:
  "lp (Pm_fmap (fmap_of_list xs)) = list_max (map fst [(k, v) \<leftarrow> AList.clearjunk xs. v \<noteq> 0])"
proof -
  have "keys (Pm_fmap (fmap_of_list xs)) = fst ` {x \<in> set (AList.clearjunk xs). case x of (k, v) \<Rightarrow> v \<noteq> 0}"
    by (auto simp: compute_keys_pp fmdom'_clearjunk0 fmap_of_list.rep_eq
        in_set_clearjunk_iff_map_of_eq_Some fmdom'I image_iff fmlookup_dom'_iff)
  then show ?thesis
    unfolding lp_def
    by (auto simp: Pm_fmap_of_list_eq_zero_iff list_max_empty list_max_nonempty)
qed

lemma compute_higher_poly_mapping[code]:
  "higher (Pm_fmap xs) t = Pm_fmap (fmfilter (\<lambda>k. t \<prec> k) xs)"
  unfolding higher_def compute_except_poly_mapping
  by (metis mem_Collect_eq ordered_powerprod_lin.leD ordered_powerprod_lin.leI)

lemma compute_lower_poly_mapping[code]:
  "lower (Pm_fmap xs) t = Pm_fmap (fmfilter (\<lambda>k. k \<prec> t) xs)"
  unfolding lower_def compute_except_poly_mapping
  by (metis mem_Collect_eq ordered_powerprod_lin.leD ordered_powerprod_lin.leI)

end (* ordered_powerprod *)

lifting_update poly_mapping.lifting
lifting_forget poly_mapping.lifting

end (* theory *)
