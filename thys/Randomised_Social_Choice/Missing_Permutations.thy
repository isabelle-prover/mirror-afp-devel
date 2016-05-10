theory Missing_Permutations
imports 
  Missing_Multiset
  "~~/src/HOL/Library/Permutations"
begin

lemma permutes_not_in:
  assumes "f permutes S" "x \<notin> S" shows "f x = x"
  using assms by (auto simp: permutes_def)

lemma permutes_vimage: "f permutes A \<Longrightarrow> f -` A = A"
  by (simp add: bij_vimage_eq_inv_image permutes_bij permutes_image[OF permutes_inv])

lemma permutes_inj_on: "f permutes S \<Longrightarrow> inj_on f A"
  unfolding permutes_def inj_on_def by auto

lemma inj_on_image: "inj_on f (\<Union>A) \<Longrightarrow> inj_on (op ` f) A"
  unfolding inj_on_def by blast

lemma disjoint_image: "inj_on f (\<Union>A) \<Longrightarrow> disjoint A \<Longrightarrow> disjoint (op ` f ` A)"
  unfolding inj_on_def disjoint_def by blast

lemma map_of_permute: 
  assumes "\<sigma> permutes fst ` set xs"
  shows   "map_of xs \<circ> \<sigma> = map_of (map (\<lambda>(x,y). (inv \<sigma> x, y)) xs)" (is "_ = map_of (map ?f _)")
proof
  fix x
  from assms have "inj \<sigma>" "surj \<sigma>" by (simp_all add: permutes_inj permutes_surj)
  thus "(map_of xs \<circ> \<sigma>) x = map_of (map ?f xs) x"
    by (induction xs) (auto simp: inv_f_f surj_f_inv_f)
qed

definition permute_list :: "(nat \<Rightarrow> nat) \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "permute_list f xs = map (\<lambda>i. xs ! (f i)) [0..<length xs]"

lemma permute_list_map: 
  assumes "f permutes {..<length xs}"
  shows   "permute_list f (map g xs) = map g (permute_list f xs)"
  using permutes_in_image[OF assms] by (auto simp: permute_list_def)

lemma permute_list_nth:
  assumes "f permutes {..<length xs}" "i < length xs"
  shows   "permute_list f xs ! i = xs ! f i"
  using permutes_in_image[OF assms(1)] assms(2) 
  by (simp add: permute_list_def)

lemma permute_list_Nil [simp]: "permute_list f [] = []"
  by (simp add: permute_list_def)

lemma length_permute_list [simp]: "length (permute_list f xs) = length xs"
  by (simp add: permute_list_def)

lemma permute_list_compose: 
  assumes "g permutes {..<length xs}"
  shows   "permute_list (f \<circ> g) xs = permute_list g (permute_list f xs)"
  using assms[THEN permutes_in_image] by (auto simp add: permute_list_def)

lemma permute_list_ident [simp]: "permute_list (\<lambda>x. x) xs = xs"
  by (simp add: permute_list_def map_nth)

lemma permute_list_id [simp]: "permute_list id xs = xs"
  by (simp add: id_def)

lemma mset_upt [simp]: "mset [m..<n] = mset_set {m..<n}"
  by (induction n) (simp_all add: atLeastLessThanSuc add_ac)

lemma mset_permute_list [simp]:
  assumes "f permutes {..<length (xs :: 'a list)}"
  shows   "mset (permute_list f xs) = mset xs"
proof (rule multiset_eqI)
  fix y :: 'a
  from assms have [simp]: "f x < length xs \<longleftrightarrow> x < length xs" for x
    using permutes_in_image[OF assms] by auto
  have "count (mset (permute_list f xs)) y = 
          card ((\<lambda>i. xs ! f i) -` {y} \<inter> {..<length xs})"
    by (simp add: permute_list_def mset_map count_image_mset atLeast0LessThan)
  also have "(\<lambda>i. xs ! f i) -` {y} \<inter> {..<length xs} = f -` {i. i < length xs \<and> y = xs ! i}"
    by auto
  also from assms have "card \<dots> = card {i. i < length xs \<and> y = xs ! i}"
    by (intro card_vimage_inj) (auto simp: permutes_inj permutes_surj)
  also have "\<dots> = count (mset xs) y" by (simp add: count_mset length_filter_conv_card)
  finally show "count (mset (permute_list f xs)) y = count (mset xs) y" by simp
qed

lemma set_permute_list [simp]:
  assumes "f permutes {..<length xs}"
  shows   "set (permute_list f xs) = set xs"
  by (rule mset_eq_setD[OF mset_permute_list]) fact

lemma distinct_permute_list [simp]:
  assumes "f permutes {..<length xs}"
  shows   "distinct (permute_list f xs) = distinct xs"
  by (simp add: distinct_count_atmost_1 assms)

lemma mset_eq_permutation:
  assumes mset_eq: "mset (xs::'a list) = mset ys"
  defines [simp]: "n \<equiv> length xs"
  obtains f where "f permutes {..<length ys}" "permute_list f ys = xs"
proof -
  from mset_eq have [simp]: "length xs = length ys"
    by (rule mset_eq_length)
  def indices_of \<equiv> "\<lambda>(x::'a) xs. {i. i < length xs \<and> x = xs ! i}"
  have indices_of_subset: "indices_of x xs \<subseteq> {..<length xs}" for x xs
    unfolding indices_of_def by blast
  have [simp]: "finite (indices_of x xs)" for x xs
    by (rule finite_subset[OF indices_of_subset]) simp_all

  have "\<forall>x\<in>set xs. \<exists>f. bij_betw f (indices_of x xs) (indices_of x ys)"
  proof
    fix x
    from mset_eq have "count (mset xs) x = count (mset ys) x" by simp
    hence "card (indices_of x xs) = card (indices_of x ys)"
      by (simp add: count_mset length_filter_conv_card indices_of_def)
    thus "\<exists>f. bij_betw f (indices_of x xs) (indices_of x ys)"
      by (intro finite_same_card_bij) simp_all
  qed
  hence "\<exists>f. \<forall>x\<in>set xs. bij_betw (f x) (indices_of x xs) (indices_of x ys)"
    by (rule bchoice)
  then guess f .. note f = this
  def g \<equiv> "\<lambda>i. if i < n then f (xs ! i) i else i"

  have bij_f: "bij_betw (\<lambda>i. f (xs ! i) i) (indices_of x xs) (indices_of x ys)"
    if x: "x \<in> set xs" for x
  proof (subst bij_betw_cong)
    from f x show "bij_betw (f x) (indices_of x xs) (indices_of x ys)" by blast
    fix i assume "i \<in> indices_of x xs"
    thus "f (xs ! i) i = f x i" by (simp add: indices_of_def)
  qed

  hence "bij_betw (\<lambda>i. f (xs ! i) i) (\<Union>x\<in>set xs. indices_of x xs) (\<Union>x\<in>set xs. indices_of x ys)"
    by (intro bij_betw_UNION_disjoint) (auto simp add: disjoint_family_on_def indices_of_def)
  also have "(\<Union>x\<in>set xs. indices_of x xs) = {..<n}" by (auto simp: indices_of_def)
  also from mset_eq have "set xs = set ys" by (rule mset_eq_setD) 
  also have "(\<Union>x\<in>set ys. indices_of x ys) = {..<n}"
    by (auto simp: indices_of_def set_conv_nth)
  also have "bij_betw (\<lambda>i. f (xs ! i) i) {..<n} {..<n} \<longleftrightarrow> bij_betw g {..<n} {..<n}"
    by (intro bij_betw_cong) (simp_all add: g_def)
  finally have "g permutes {..<length ys}"
    by (intro bij_imp_permutes refl) (simp_all add: g_def)

  moreover have "permute_list g ys = xs" 
  proof (rule sym, intro nth_equalityI allI impI)
    fix i assume i: "i < length xs"
    from i have "permute_list g ys ! i = ys ! f (xs ! i) i"
      by (simp add: permute_list_def g_def)
    also from i have "i \<in> indices_of (xs ! i) xs" by (simp add: indices_of_def)
    with bij_f[of "xs ! i"] i have "f (xs ! i) i \<in> indices_of (xs ! i) ys"
      by (auto simp: bij_betw_def)
    hence "ys ! f (xs ! i) i = xs ! i" by (simp add: indices_of_def)
    finally show "xs ! i = permute_list g ys ! i" ..
  qed simp_all

  ultimately show ?thesis by (rule that)
qed

lemma distinct_Ex1: 
  "distinct xs \<Longrightarrow> x \<in> set xs \<Longrightarrow> (\<exists>!i. i < length xs \<and> xs ! i = x)"
  by (auto simp: in_set_conv_nth nth_eq_iff_index_eq)

lemma bij_betw_nth:
  assumes "distinct xs" "A = {..<length xs}" "B = set xs" 
  shows   "bij_betw (op ! xs) A B"
  using assms unfolding bij_betw_def
  by (auto intro!: inj_on_nth simp: set_conv_nth)

lemma permutes_invI: 
  assumes perm: "p permutes S"
      and inv:  "\<And>x. x \<in> S \<Longrightarrow> p' (p x) = x" 
      and outside: "\<And>x. x \<notin> S \<Longrightarrow> p' x = x"
  shows   "inv p = p'"
proof
  fix x show "inv p x = p' x"
  proof (cases "x \<in> S")
    assume [simp]: "x \<in> S"
    from assms have "p' x = p' (p (inv p x))" by (simp add: permutes_inverses)
    also from permutes_inv[OF perm] 
      have "\<dots> = inv p x" by (subst inv) (simp_all add: permutes_in_image)
    finally show "inv p x = p' x" ..
  qed (insert permutes_inv[OF perm], simp_all add: outside permutes_not_in)
qed

lemma permute_list_zip: 
  assumes "f permutes A" "A = {..<length xs}"
  assumes [simp]: "length xs = length ys"
  shows   "permute_list f (zip xs ys) = zip (permute_list f xs) (permute_list f ys)"
proof -
  from permutes_in_image[OF assms(1)] assms(2)
    have [simp]: "f i < length ys \<longleftrightarrow> i < length ys" for i by simp
  have "permute_list f (zip xs ys) = map (\<lambda>i. zip xs ys ! f i) [0..<length ys]"
    by (simp_all add: permute_list_def zip_map_map)
  also have "\<dots> = map (\<lambda>(x, y). (xs ! f x, ys ! f y)) (zip [0..<length ys] [0..<length ys])"
    by (intro nth_equalityI) simp_all
  also have "\<dots> = zip (permute_list f xs) (permute_list f ys)"
    by (simp_all add: permute_list_def zip_map_map)
  finally show ?thesis .
qed


definition list_permutes where
  "list_permutes xs A \<longleftrightarrow> set (map fst xs) \<subseteq> A \<and> set (map snd xs) = set (map fst xs) \<and> 
     distinct (map fst xs) \<and> distinct (map snd xs)"

lemma list_permutesI [simp]:
  assumes "set (map fst xs) \<subseteq> A" "set (map snd xs) = set (map fst xs)" "distinct (map fst xs)"
  shows   "list_permutes xs A"
proof -
  from assms(2,3) have "distinct (map snd xs)"
    by (intro card_distinct) (simp_all add: distinct_card del: set_map)
  with assms show ?thesis by (simp add: list_permutes_def)
qed

definition permutation_of_list where
  "permutation_of_list xs x = (case map_of xs x of None \<Rightarrow> x | Some y \<Rightarrow> y)"

lemma permutation_of_list_Cons:
  "permutation_of_list ((x,y) # xs) x' = (if x = x' then y else permutation_of_list xs x')"
  by (simp add: permutation_of_list_def)

fun inverse_permutation_of_list where
  "inverse_permutation_of_list [] x = x"
| "inverse_permutation_of_list ((y,x')#xs) x =
     (if x = x' then y else inverse_permutation_of_list xs x)"

declare inverse_permutation_of_list.simps [simp del]

lemma inj_on_map_of:
  assumes "distinct (map snd xs)"
  shows   "inj_on (map_of xs) (set (map fst xs))"
proof (rule inj_onI)
  fix x y assume xy: "x \<in> set (map fst xs)" "y \<in> set (map fst xs)"
  assume eq: "map_of xs x = map_of xs y"
  from xy obtain x' y' 
    where x'y': "map_of xs x = Some x'" "map_of xs y = Some y'" 
    by (cases "map_of xs x"; cases "map_of xs y")
       (simp_all add: map_of_eq_None_iff)
  moreover from this x'y' have "(x,x') \<in> set xs" "(y,y') \<in> set xs"
    by (force dest: map_of_SomeD)+
  moreover from this eq x'y' have "x' = y'" by simp
  ultimately show "x = y" using assms
    by (force simp: distinct_map dest: inj_onD[of _ _ "(x,x')" "(y,y')"])
qed

lemma inj_on_the: "None \<notin> A \<Longrightarrow> inj_on the A"
  by (auto simp: inj_on_def option.the_def split: option.splits)

lemma inj_on_map_of':
  assumes "distinct (map snd xs)"
  shows   "inj_on (the \<circ> map_of xs) (set (map fst xs))"
  by (intro comp_inj_on inj_on_map_of assms inj_on_the)
     (force simp: eq_commute[of None] map_of_eq_None_iff)

lemma image_map_of:
  assumes "distinct (map fst xs)"
  shows   "map_of xs ` set (map fst xs) = Some ` set (map snd xs)"
  using assms by (auto simp: rev_image_eqI)

lemma the_Some_image [simp]: "the ` Some ` A = A"
  by (subst image_image) simp

lemma image_map_of':
  assumes "distinct (map fst xs)"
  shows   "(the \<circ> map_of xs) ` set (map fst xs) = set (map snd xs)"
  by (simp only: image_comp [symmetric] image_map_of assms the_Some_image)

lemma permutation_of_list_permutes [simp]:
  assumes "list_permutes xs A"
  shows   "permutation_of_list xs permutes A" (is "?f permutes _")
proof (rule permutes_subset[OF bij_imp_permutes])
  from assms show "set (map fst xs) \<subseteq> A"
    by (simp add: list_permutes_def)
  from assms have "inj_on (the \<circ> map_of xs) (set (map fst xs))" (is ?P)
    by (intro inj_on_map_of') (simp_all add: list_permutes_def)
  also have "?P \<longleftrightarrow> inj_on ?f (set (map fst xs))"
    by (intro inj_on_cong)
       (auto simp: permutation_of_list_def map_of_eq_None_iff split: option.splits)
  finally have "bij_betw ?f (set (map fst xs)) (?f ` set (map fst xs))"
    by (rule inj_on_imp_bij_betw)
  also from assms have "?f ` set (map fst xs) = (the \<circ> map_of xs) ` set (map fst xs)"
    by (intro image_cong refl)
       (auto simp: permutation_of_list_def map_of_eq_None_iff split: option.splits)
  also from assms have "\<dots> = set (map fst xs)" 
    by (subst image_map_of') (simp_all add: list_permutes_def)
  finally show "bij_betw ?f (set (map fst xs)) (set (map fst xs))" .
qed (force simp: permutation_of_list_def dest!: map_of_SomeD split: option.splits)+

lemma eval_permutation_of_list [simp]:
  "permutation_of_list [] x = x"
  "x = x' \<Longrightarrow> permutation_of_list ((x',y)#xs) x = y"
  "x \<noteq> x' \<Longrightarrow> permutation_of_list ((x',y')#xs) x = permutation_of_list xs x"
  by (simp_all add: permutation_of_list_def)

lemma eval_inverse_permutation_of_list [simp]:
  "inverse_permutation_of_list [] x = x"
  "x = x' \<Longrightarrow> inverse_permutation_of_list ((y,x')#xs) x = y"
  "x \<noteq> x' \<Longrightarrow> inverse_permutation_of_list ((y',x')#xs) x = inverse_permutation_of_list xs x"
  by (simp_all add: inverse_permutation_of_list.simps)

lemma permutation_of_list_id:
  assumes "x \<notin> set (map fst xs)"
  shows   "permutation_of_list xs x = x"
  using assms by (induction xs) (auto simp: permutation_of_list_Cons)

lemma permutation_of_list_unique':
  assumes "distinct (map fst xs)" "(x, y) \<in> set xs"
  shows   "permutation_of_list xs x = y"
  using assms by (induction xs) (force simp: permutation_of_list_Cons)+

lemma permutation_of_list_unique:
  assumes "list_permutes xs A" "(x,y) \<in> set xs"
  shows   "permutation_of_list xs x = y"
  using assms by (intro permutation_of_list_unique') (simp_all add: list_permutes_def)

lemma inverse_permutation_of_list_id:
  assumes "x \<notin> set (map snd xs)"
  shows   "inverse_permutation_of_list xs x = x"
  using assms by (induction xs) auto

lemma inverse_permutation_of_list_unique':
  assumes "distinct (map snd xs)" "(x, y) \<in> set xs"
  shows   "inverse_permutation_of_list xs y = x"
  using assms by (induction xs) (force simp: inverse_permutation_of_list.simps)+

lemma inverse_permutation_of_list_unique:
  assumes "list_permutes xs A" "(x,y) \<in> set xs"
  shows   "inverse_permutation_of_list xs y = x"
  using assms by (intro inverse_permutation_of_list_unique') (simp_all add: list_permutes_def)

lemma inverse_permutation_of_list_correct:
  assumes "list_permutes xs (A :: 'a set)"
  shows   "inverse_permutation_of_list xs = inv (permutation_of_list xs)"
proof (rule ext, rule sym, subst permutes_inv_eq)
  from assms show "permutation_of_list xs permutes A" by simp
next
  fix x
  show "permutation_of_list xs (inverse_permutation_of_list xs x) = x"
  proof (cases "x \<in> set (map snd xs)")
    case True
    then obtain y where "(y, x) \<in> set xs" by force
    with assms show ?thesis
      by (simp add: inverse_permutation_of_list_unique permutation_of_list_unique)
  qed (insert assms, auto simp: list_permutes_def
         inverse_permutation_of_list_id permutation_of_list_id)
qed  

end