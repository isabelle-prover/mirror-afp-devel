(* General executable permutations *)

theory GPerm
imports
  "~~/src/HOL/Library/Quotient_Syntax"
  "~~/src/HOL/Library/Product_ord"
  "~~/src/HOL/Library/List_lexord"
begin

definition perm_apply where
  "perm_apply l e = (case [a\<leftarrow>l . fst a = e] of [] \<Rightarrow> e | x # xa \<Rightarrow> snd x)"

lemma perm_apply_simps[simp]:
  "perm_apply (h # t) e = (if fst h = e then snd h else perm_apply t e)"
  "perm_apply [] e = e"
  by (auto simp add: perm_apply_def)

definition valid_perm where
  "valid_perm p \<longleftrightarrow> distinct (map fst p) \<and> fst ` set p = snd ` set p"

lemma valid_perm_zero[simp]:
  "valid_perm []"
  by (simp add: valid_perm_def)

lemma length_eq_card_distinct:
  "length l = card (set l) \<longleftrightarrow> distinct l"
  using card_distinct distinct_card by force

lemma len_set_eq_distinct:
  assumes "length l = length m" "set l = set m"
  shows "distinct l = distinct m"
  using assms
  by (simp add: length_eq_card_distinct[symmetric])

lemma valid_perm_distinct_snd: "valid_perm a \<Longrightarrow> distinct (map snd a)"
  by (metis valid_perm_def image_set length_map len_set_eq_distinct)

definition
  perm_eq :: "('a \<times> 'a) list \<Rightarrow> ('a \<times> 'a) list \<Rightarrow> bool"
where
  "perm_eq x y \<longleftrightarrow> valid_perm x \<and> valid_perm y \<and> (perm_apply x = perm_apply y)"

lemma perm_eq_sym[sym]:
  "perm_eq x y \<Longrightarrow> perm_eq y x"
  by (auto simp add: perm_eq_def)

lemma perm_eq_equivp:
  "part_equivp perm_eq"
  by (auto intro!: part_equivpI sympI transpI exI[of _ "[]"] simp add: perm_eq_def)

quotient_type
  'a gperm = "('a \<times> 'a) list" / partial: "perm_eq"
  by (rule perm_eq_equivp)

definition perm_add_raw where
  "perm_add_raw p q = map (map_prod id (perm_apply p)) q @ [a\<leftarrow>p. fst a \<notin> fst ` set q]"

lemma perm_apply_del[simp]:
  "e \<noteq> b \<Longrightarrow> perm_apply [a\<leftarrow>l. fst a \<noteq> b] e = perm_apply l e"
  "e \<noteq> b \<Longrightarrow> e \<noteq> c \<Longrightarrow> perm_apply [a\<leftarrow>l . fst a \<noteq> b \<and> fst a \<noteq> c] e = perm_apply l e"
  by (induct l) auto

lemma perm_apply_appendl:
  "perm_apply a e = perm_apply b e \<Longrightarrow> perm_apply (c @ a) e = perm_apply (c @ b) e"
  by (induct c) auto

lemma perm_apply_filterP:
  "b \<noteq> e \<Longrightarrow> perm_apply [a\<leftarrow>l . fst a \<noteq> b \<and> P a] e = perm_apply [a\<leftarrow>l . P a] e"
  by (induct l) auto

lemma perm_add_apply:
  shows "perm_apply (perm_add_raw p q) e = perm_apply p (perm_apply q e)"
  by (rule sym, induct q)
     (auto simp add: perm_add_raw_def perm_apply_filterP intro!: perm_apply_appendl)

definition swap_pair where
  "swap_pair a = (snd a, fst a)"

definition uminus_perm_raw where
  [simp]: "uminus_perm_raw = map swap_pair"

lemma map_fst_minus_perm[simp]:
  "map fst (uminus_perm_raw x) = map snd x"
  "map snd (uminus_perm_raw x) = map fst x"
  by (induct x) (auto simp add: swap_pair_def)

lemma fst_snd_set_minus_perm[simp]:
  "fst ` set (uminus_perm_raw x) = snd ` set x"
  "snd ` set (uminus_perm_raw x) = fst ` set x"
  by (induct x) (auto simp add: swap_pair_def)

lemma fst_snd_swap_pair[simp]:
  "fst (swap_pair x) = snd x"
  "snd (swap_pair x) = fst x"
  by (auto simp add: swap_pair_def)

lemma fst_snd_swap_pair_set[simp]:
  "fst ` swap_pair ` set l = snd ` set l"
  "snd ` swap_pair ` set l = fst ` set l"
  by (induct l) (auto simp add: swap_pair_def)

lemma valid_perm_minus[simp]:
  assumes "valid_perm x"
  shows "valid_perm (map swap_pair x)"
  using assms unfolding valid_perm_def
  by (simp add: valid_perm_distinct_snd[OF assms] o_def)

lemma swap_pair_id[simp]:
  "swap_pair (swap_pair x) = x"
  unfolding swap_pair_def by simp

lemma perm_apply_minus_minus[simp]:
  "perm_apply (uminus_perm_raw (uminus_perm_raw x)) = perm_apply x"
  by (simp add: o_def)

lemma filter_eq_nil:
  "[a\<leftarrow>a. fst a = e] = [] \<longleftrightarrow> e \<notin> fst ` set a"
  "[a\<leftarrow>a. snd a = e] = [] \<longleftrightarrow> e \<notin> snd ` set a"
  by (induct a) auto

lemma filter_rev_eq_nil: "[a\<leftarrow>map swap_pair a. fst a = e] = [] \<longleftrightarrow> e \<notin> snd ` set a"
  by (induct a) (auto simp add: swap_pair_def)

lemma filter_fst_eq:
  "[a\<leftarrow>a . fst a = e] = (l, r) # list \<Longrightarrow> l = e"
  "[a\<leftarrow>a . snd a = e] = (l, r) # list \<Longrightarrow> r = e"
  by (drule filter_eq_ConsD, auto)+

lemma filter_map_swap_pair:
  "[a\<leftarrow>map swap_pair a. fst a = e] = map swap_pair [a\<leftarrow>a. snd a = e]"
  by (induct a) auto

lemma forget_tl:
  "[a\<leftarrow>l . P a] = a # b \<Longrightarrow> a \<in> set l"
  by (metis Cons_eq_filter_iff in_set_conv_decomp)

lemma valid_perm_lookup_fst_eq_snd:
  "[a\<leftarrow>l . fst a = f] = (f, s) # l1 \<Longrightarrow> [a\<leftarrow>l . snd a = s] = (f2, s) # l2 \<Longrightarrow> valid_perm l \<Longrightarrow> f2 = f"
  apply (drule forget_tl valid_perm_distinct_snd)+
  apply (case_tac "f2 = f")
  apply (auto simp add: in_set_conv_nth swap_pair_def)
  apply (case_tac "i = ia")
  apply auto
  by (metis length_map nth_eq_iff_index_eq nth_map snd_conv)

lemma valid_perm_add_minus: "valid_perm a \<Longrightarrow> perm_apply (map swap_pair a) (perm_apply a e) = e"
  apply (auto simp add: filter_map_swap_pair filter_eq_nil filter_rev_eq_nil perm_apply_def split: list.split)
  apply (metis filter_eq_nil(2) neq_Nil_conv valid_perm_def)
  apply (metis list.sel(1) hd_in_set image_eqI list.simps(2) member_project project_set snd_conv)
  apply (frule filter_fst_eq(1))
  apply (frule filter_fst_eq(2))
  apply (auto simp add: swap_pair_def)
  apply (erule valid_perm_lookup_fst_eq_snd)
  apply assumption+
  done

lemma perm_apply_minus: "valid_perm x \<Longrightarrow> perm_apply (map swap_pair x) a = b \<longleftrightarrow> perm_apply x b = a"
  using valid_perm_add_minus[symmetric] valid_perm_minus
  by (metis uminus_perm_raw_def)

lemma uminus_perm_raw_rsp[simp]:
  "perm_eq x y \<Longrightarrow> perm_eq (map swap_pair x) (map swap_pair y)"
  by (auto simp add: fun_eq_iff perm_apply_minus[symmetric] perm_eq_def)

lemma fst_snd_map_prod[simp]:
  "fst ` map_prod f g ` set l = f ` fst ` set l"
  "snd ` map_prod f g ` set l = g ` snd ` set l"
  by (induct l) auto

lemma fst_diff[simp]:
  shows "fst ` {xa \<in> set x. fst xa \<notin> fst ` set y} = fst ` set x - fst ` set y"
  by auto

lemma pair_perm_apply:
  "distinct (map fst x) \<Longrightarrow> (a, b) \<in> set x \<Longrightarrow> perm_apply x a = b"
  by (induct x) (auto, metis fst_conv image_eqI)

lemma valid_perm_apply:
  "valid_perm x \<Longrightarrow> (a, b) \<in> set x \<Longrightarrow> perm_apply x a = b"
  unfolding valid_perm_def using pair_perm_apply by auto

lemma in_perm_apply:
  "valid_perm x \<Longrightarrow> (a, b) \<in> set x \<Longrightarrow> a \<in> c \<Longrightarrow> b \<in> perm_apply x ` c"
  by (metis imageI valid_perm_apply)

lemma snd_set_not_in_perm_apply[simp]:
  assumes "valid_perm x"
  shows "snd ` {xa \<in> set x. fst xa \<notin> fst ` set y} = perm_apply x ` (fst ` set x - fst ` set y)"
proof auto
  fix a b
  assume a: "(a, b) \<in> set x" " a \<notin> fst ` set y"
  then have "a \<in> fst ` set x - fst ` set y"
    by simp (metis fst_conv image_eqI)
  with a show "b \<in> perm_apply x ` (fst ` set x - fst ` set y)"
    by (simp add: in_perm_apply assms)
next
  fix a b
  assume a: "a \<notin> fst ` set y" "(a, b) \<in> set x"
  then have "perm_apply x a = b"
    by (simp add: valid_perm_apply assms)
  with a show "perm_apply x a \<in> snd ` {xa \<in> set x. fst xa \<notin> fst ` set y}"
    by (metis (lifting) CollectI fst_conv image_eqI snd_conv)
qed

lemma perm_apply_set:
  "valid_perm x \<Longrightarrow> perm_apply x ` fst ` set x = fst ` set x"
  by (auto simp add: valid_perm_def)
     (metis (hide_lams, no_types) image_iff pair_perm_apply snd_eqD surjective_pairing)+

lemma perm_apply_outset: "a \<notin> fst ` set x \<Longrightarrow> perm_apply x a = a"
  by (induct x) auto

lemma perm_apply_subset: "valid_perm x \<Longrightarrow> fst ` set x \<subseteq> s \<Longrightarrow> perm_apply x ` s = s"
  apply auto
  apply (case_tac [!] "xa \<in> fst ` set x")
  apply (metis imageI perm_apply_set subsetD)
  apply (metis perm_apply_outset)
  apply (metis image_mono perm_apply_set subsetD)
  by (metis imageI perm_apply_outset)

lemma valid_perm_add_raw[simp]:
  assumes "valid_perm x" "valid_perm y"
  shows "valid_perm (perm_add_raw x y)"
  using assms
  apply (simp (no_asm) add: valid_perm_def)
  apply (intro conjI)
  apply (auto simp add: perm_add_raw_def valid_perm_def fst_def[symmetric])[1]
  apply (simp add: distinct_map inj_on_def)
  apply (metis imageI snd_conv)
  apply (simp add: perm_add_raw_def image_Un)
  apply (simp add: image_Un[symmetric])
  apply (auto simp add: perm_apply_subset valid_perm_def)
  done

lemma perm_add_raw_rsp[simp]:
  "perm_eq x y \<Longrightarrow> perm_eq xa ya \<Longrightarrow> perm_eq (perm_add_raw x xa) (perm_add_raw y ya)"
  by (simp add: fun_eq_iff perm_add_apply perm_eq_def)

lemma [simp]:
  "perm_eq a a \<longleftrightarrow> valid_perm a"
  by (simp_all add: perm_eq_def)

instantiation gperm :: (type) group_add
begin

lift_definition zero_gperm :: "'a gperm" is "[]" by simp

lift_definition uminus_gperm :: "'a gperm \<Rightarrow> 'a gperm" is uminus_perm_raw
  by (auto simp add: fun_eq_iff perm_apply_minus[symmetric] perm_eq_def)

lift_definition plus_gperm :: "'a gperm \<Rightarrow> 'a gperm \<Rightarrow> 'a gperm" is perm_add_raw
  by simp

definition
  minus_perm_def: "(p1::'a gperm) - p2 = p1 + - p2"

instance
  apply default
  unfolding minus_perm_def
  by (transfer,simp add: perm_add_apply perm_eq_def fun_eq_iff valid_perm_add_minus)+

end

definition "mk_perm_raw l = (if valid_perm l then l else [])"

lift_definition mk_perm :: "('a \<times> 'a) list \<Rightarrow> 'a gperm" is "mk_perm_raw"
  by (simp add: mk_perm_raw_def)

definition "dest_perm_raw p = sort [x\<leftarrow>p. fst x \<noteq> snd x]"

lemma distinct_fst_distinct[simp]: "distinct (map fst x) \<Longrightarrow> distinct x"
  by (induct x) auto

lemma perm_apply_in_set:
  "a \<noteq> b \<Longrightarrow> perm_apply y a = b \<Longrightarrow> (a, b) \<in> set y"
  by (induct y) (auto split: if_splits)

lemma perm_eq_not_eq_same:
  "perm_eq x y \<Longrightarrow> {xa \<in> set x. fst xa \<noteq> snd xa} = {x \<in> set y. fst x \<noteq> snd x}"
  unfolding perm_eq_def set_eq_iff
  apply auto
  apply (subgoal_tac "perm_apply x a = b")
  apply (simp add: perm_apply_in_set)
  apply (erule valid_perm_apply)
  apply simp
  apply (subgoal_tac "perm_apply y a = b")
  apply (simp add: perm_apply_in_set)
  apply (erule valid_perm_apply)
  apply simp
  done

lemma [simp]: "distinct (map fst (sort x)) = distinct (map fst x)"
  by (rule len_set_eq_distinct) simp_all

lemma valid_perm_sort[simp]:
  "valid_perm x \<Longrightarrow> valid_perm (sort x)"
  unfolding valid_perm_def by simp

lemma same_not_in_dpr:
  "valid_perm x \<Longrightarrow> (b, b) \<in> set x \<Longrightarrow> b \<notin> fst ` set (dest_perm_raw x)"
  unfolding dest_perm_raw_def valid_perm_def
  by auto (metis pair_perm_apply)

lemma in_set_in_dpr:
  "valid_perm x \<Longrightarrow> a \<noteq> b \<Longrightarrow> (a, b) \<in> set x \<longleftrightarrow> (a, b) \<in> set (dest_perm_raw x)"
  unfolding dest_perm_raw_def valid_perm_def
  by simp

lemma in_set_in_dpr2:
  "a \<noteq> b \<Longrightarrow> (dest_perm_raw x = dest_perm_raw y) \<Longrightarrow> valid_perm x \<Longrightarrow> valid_perm y \<Longrightarrow> (a, b) \<in> set x \<longleftrightarrow> (a, b) \<in> set y"
  using in_set_in_dpr by metis

lemma in_set_in_dpr3:
  "(dest_perm_raw x = dest_perm_raw y) \<Longrightarrow> valid_perm x \<Longrightarrow> valid_perm y \<Longrightarrow> perm_apply x a = perm_apply y a"
  by (metis in_set_in_dpr2 pair_perm_apply perm_apply_in_set valid_perm_def)

lemma dest_perm_raw_eq[simp]:
  "valid_perm x \<Longrightarrow> valid_perm y \<Longrightarrow> (dest_perm_raw x = dest_perm_raw y) = perm_eq x y"
  apply (auto simp add: perm_eq_def)
  apply (metis in_set_in_dpr3 fun_eq_iff)
  unfolding dest_perm_raw_def
  by (rule sorted_distinct_set_unique)
     (simp_all add: distinct_filter valid_perm_def perm_eq_not_eq_same[simplified perm_eq_def, simplified])

lift_definition dest_perm :: "('a :: linorder) gperm \<Rightarrow> ('a \<times> 'a) list"
  is "dest_perm_raw"
  by (simp add: perm_eq_def)

lemma dest_perm_mk_perm[simp]:
  "dest_perm (mk_perm xs) = sort [x\<leftarrow>mk_perm_raw xs. fst x \<noteq> snd x]"
  by transfer (simp add: dest_perm_raw_def)

lemma valid_perm_filter_id[simp]:
  "valid_perm p \<Longrightarrow> valid_perm [x\<leftarrow>p. fst x \<noteq> snd x]"
proof (simp (no_asm) add: valid_perm_def, intro conjI)
  show "valid_perm p \<Longrightarrow> distinct (map fst [x\<Colon>'a \<times> 'a\<leftarrow>p . fst x \<noteq> snd x])"
    by (auto simp add: distinct_map inj_on_def valid_perm_def)
  assume a: "valid_perm p"
  then show "fst ` {x\<Colon>'a \<times> 'a \<in> set p. fst x \<noteq> snd x} = snd ` {x\<Colon>'a \<times> 'a \<in> set p. fst x \<noteq> snd x}"
    apply -
    apply (frule valid_perm_distinct_snd)
    apply (simp add: valid_perm_def)
    apply auto
    apply (subgoal_tac "a \<in> snd ` set p")
    apply auto
    apply (subgoal_tac "(aa, ba) \<in> {x \<in> set p. fst x \<noteq> snd x}")
    apply (metis (lifting) image_eqI snd_conv)
    apply (metis (lifting, mono_tags) fst_conv mem_Collect_eq snd_conv pair_perm_apply)
    apply (metis fst_conv imageI)
    apply (drule sym)
    apply (subgoal_tac "b \<in> fst ` set p")
    apply auto
    apply (subgoal_tac "(aa, ba) \<in> {x \<in> set p. fst x \<noteq> snd x}")
    apply (metis (lifting) image_eqI fst_conv)
    apply simp
    apply (metis valid_perm_add_minus valid_perm_apply valid_perm_def)
    apply (metis snd_conv imageI)
    done
qed

lemma valid_perm_dest_pair_raw[simp]:
  assumes "valid_perm x"
  shows "valid_perm (dest_perm_raw x)"
  using valid_perm_filter_id valid_perm_sort assms
  unfolding dest_perm_raw_def
  by simp

lemma dest_perm_raw_repeat[simp]:
  "dest_perm_raw (dest_perm_raw p) = dest_perm_raw p"
  unfolding dest_perm_raw_def
  by simp (rule sorted_sort_id[OF sorted_sort])

lemma valid_dest_perm_raw_eq[simp]:
  "valid_perm p \<Longrightarrow> perm_eq (dest_perm_raw p) p"
  "valid_perm p \<Longrightarrow> perm_eq p (dest_perm_raw p)"
  by (simp_all add: dest_perm_raw_eq[symmetric])

lemma mk_perm_dest_perm[code abstype]:
  "mk_perm (dest_perm p) = p"
  by transfer
     (auto simp add: mk_perm_raw_def)

instantiation gperm :: (linorder) equal begin

definition equal_gperm_def: "equal_gperm a b \<longleftrightarrow> dest_perm a = dest_perm b"

instance
  apply default
  unfolding equal_gperm_def
  by transfer simp

end

lemma [code abstract]:
  "dest_perm 0 = []"
  by transfer (simp add: dest_perm_raw_def)

lemma [code abstract]:
  "dest_perm (-a) = dest_perm_raw (uminus_perm_raw (dest_perm a))"
  by transfer auto

lemma [code abstract]:
  "dest_perm (a + b) = dest_perm_raw (perm_add_raw (dest_perm a) (dest_perm b))"
  by transfer auto

lift_definition gpermute :: "'a gperm \<Rightarrow> 'a \<Rightarrow> 'a"
  is perm_apply
  by (simp add: perm_eq_def)

lemma gpermute_zero[simp]:
  "gpermute 0 x = x"
  by transfer simp

lemma gpermute_add[simp]:
  "gpermute (p + q) x = gpermute p (gpermute q x)"
  by transfer (simp add: perm_add_apply)

definition [simp]: "swap_raw a b = (if a = b then [] else [(a, b), (b, a)])"

lift_definition gswap :: "'a \<Rightarrow> 'a \<Rightarrow> 'a gperm" is swap_raw
  by (auto simp add: valid_perm_def)

lemma [code abstract]:
  "dest_perm (gswap a b) = (if (a, b) \<le> (b, a) then swap_raw a b else swap_raw b a)"
  by transfer (auto simp add: dest_perm_raw_def)

lemma swap_self [simp]:
  "gswap a a = 0"
  by transfer simp

lemma [simp]: "a \<noteq> b \<Longrightarrow> valid_perm [(a, b), (b, a)]"
  unfolding valid_perm_def by auto

lemma swap_cancel [simp]:
  "gswap a b + gswap a b = 0"
  "gswap a b + gswap b a = 0"
  by (transfer, auto simp add: perm_eq_def perm_add_apply)+

lemma minus_swap [simp]:
  "- gswap a b = gswap a b"
  by transfer (auto simp add: perm_eq_def)

lemma swap_commute:
  "gswap a b = gswap b a"
  by transfer (auto simp add: perm_eq_def)

lemma swap_triple:
  assumes "a \<noteq> b" "c \<noteq> b"
  shows "gswap a c + gswap b c + gswap a c = gswap a b"
  using assms
  by transfer (auto simp add: perm_eq_def fun_eq_iff perm_add_apply)

lemma gpermute_gswap[simp]:
  "b \<noteq> a \<Longrightarrow> gpermute (gswap a b) b = a"
  "a \<noteq> b \<Longrightarrow> gpermute (gswap a b) a = b"
  "c \<noteq> b \<Longrightarrow> c \<noteq> a \<Longrightarrow> gpermute (gswap a b) c = c"
  by (transfer, auto)+

lemma gperm_eq:
  "(p = q) = (\<forall>a. gpermute p a = gpermute q a)"
  by transfer (auto simp add: perm_eq_def)

lemma finite_gpermute_neq:
  "finite {a. gpermute p a \<noteq> a}"
  apply transfer
  apply (rule_tac B="fst ` set p" in finite_subset)
  apply auto
  by (metis perm_apply_outset)

end
