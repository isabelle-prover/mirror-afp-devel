theory Weighted_Set
  imports
    "HOL-Library.Multiset"
begin

section \<open>Algebraic Preliminaries\<close>

instantiation option :: (ab_semigroup_add) comm_monoid_add begin
definition zero_option where "zero_option = None"
definition plus_option where "plus_option a b = (case (a, b) of (Some x, Some y) \<Rightarrow> Some (x + y) | (Some x, None) \<Rightarrow> Some x | (None, Some x) \<Rightarrow> Some x | _ \<Rightarrow> None)"
instance
  by standard (auto simp: zero_option_def plus_option_def ac_simps split: option.splits)
end

text \<open>The notion of refinability is due to Gumm and Schröder \<^cite>\<open>"DBLP:journals/entcs/GummS01"\<close>,
  who introduced it for monoids. We generalize it to semigroups.\<close>

class ref_ab_semigroup_add = ab_semigroup_add +
  assumes refinable: "(a :: 'a :: ab_semigroup_add) + b = c + d \<Longrightarrow> 
  (\<exists> (e11 :: ('a :: ab_semigroup_add) option) e12 e21 e22. Some a = e11 + e12 \<and>
    Some b = e21 + e22 \<and> Some c = e11 + e21 \<and> Some d = e12 + e22)"

lemma plus_option_simps [simp]: "a + None = a" "None + a = a" "Some c + Some d = Some (c + d)"
  unfolding add.right_neutral add.left_neutral zero_option_def[symmetric] atomize_conj
  unfolding plus_option_def
  by simp

lemma plus_option_case: "Some e + f = Some (case f of Some f' \<Rightarrow> e + f' | None \<Rightarrow> e)" "f + Some e = Some (case f of Some f' \<Rightarrow> f' + e | None \<Rightarrow> e)"
  unfolding add.right_neutral add.left_neutral zero_option_def[symmetric] atomize_conj
  unfolding plus_option_def
  by(cases f; simp)

instantiation option :: (ref_ab_semigroup_add) ref_ab_semigroup_add begin
instance
proof intro_classes
  fix a b c d :: "'a option"
  assume A1: "a + b = c + d"
  show "\<exists>e11 e12 e21 e22. Some a = e11 + e12 \<and> Some b = e21 + e22 \<and> Some c = e11 + e21 \<and> Some d = e12 + e22"
  proof -
    consider (Some) a' b' c' d' where "a = Some a'" "b = Some b'" "c = Some c'" "d = Some d'"
      | (a) "a = None" | (b) "b = None" | (c) "c = None" | (d) "d = None"
      by fastforce
    then show ?thesis
    proof (cases)
      case Some
      then have "a' + b' = c' + d'"
        using A1 unfolding plus_option_def by auto
      from refinable[OF this] show ?thesis
        unfolding Some by (metis plus_option_simps(3))
    next
      case a
      with A1 show ?thesis by (metis plus_option_simps(1,2,3))
    next
      case b
      with A1 show ?thesis by (metis plus_option_simps(1,3))
    next
      case c
      with A1 show ?thesis by (metis plus_option_simps(1,2,3))
    next
      case d
      with A1 show ?thesis by (metis plus_option_simps(1,3))
    qed
  qed
qed
end

section \<open>The Positive Representation\<close>

abbreviation sum_key where 
  "sum_key kxs e \<equiv> fold (\<lambda>(_,w) y. Some w + y) (filter (\<lambda>(e',_). e = e') kxs) None"

definition eq_wset where
  "eq_wset (kxs :: ('a \<times> ('w :: ref_ab_semigroup_add)) list) (kys :: ('a \<times> ('w :: ref_ab_semigroup_add)) list) = 
  (\<forall> e. sum_key kxs e = sum_key kys e)"

declare [[typedef_overloaded]]

quotient_type ('a, 'w) wset = "('a \<times> 'w :: ref_ab_semigroup_add) list" / eq_wset
  by(auto intro!: equivpI reflpI sympI transpI simp: eq_wset_def)

lemma get_abs_wset: "\<exists>l. M = abs_wset l"
  by (metis Quotient3_abs_rep Quotient3_wset)

lemma fold_Some: "fold (\<lambda>(a, w). (+) (Some w)) xs (Some w) \<noteq> None" "None \<noteq> fold (\<lambda>(a, w). (+) (Some w)) xs (Some w)"
proof-
  have H: "fold (\<lambda>(a, w). (+) (Some w)) xs (Some w) \<noteq> None"
  proof(induction xs arbitrary: w)
    case Nil
    then show ?case
      by simp
  next
    case (Cons x xs)
    then show ?case
      by(cases x; simp)
  qed
  show "fold (\<lambda>(a, w). (+) (Some w)) xs (Some w) \<noteq> None"
    by(rule H)
  show "None \<noteq> fold (\<lambda>(a, w). (+) (Some w)) xs (Some w)"
    using H
    by force
qed

lemma fold_Some': "\<exists>w'. fold (\<lambda>(a, w). (+) (Some w)) xs (Some w) = Some w'"
  using fold_Some
  by auto


lemma fold_Some_out: "fold (\<lambda>(a, w). (+) (Some w)) xs (Some w) = (Some w) + fold (\<lambda>(a, w). (+) (Some w)) xs None"
proof(induction xs arbitrary: w)
  case Nil
  then show ?case
    by simp
next
  case (Cons x xs)
  then show ?case
    by(cases x; simp add: add.assoc[symmetric] add.commute)
qed


lemma eq_wset_fst: 
  assumes H: "eq_wset xs xs'"
  shows "set (map fst xs') = set (map fst xs)"
proof -
  have fold_eq: "\<forall>a. (sum_key xs a = None) = (sum_key xs' a = None)"
    using H
    unfolding eq_wset_def
    by presburger
  have fold_True: "fold (\<lambda>_ _. True) L True" for L :: "'c list"
    by(induction L; simp)
  have fold_None_set: "(sum_key xs a = None) = (a \<notin> set (map fst xs))" for a :: 'a and xs :: "('a \<times> 'b) list"
  proof (induction xs)
    case Nil
    show ?case by simp
  next
    case (Cons h t)
    obtain h1 h2 where h_def: "h = (h1, h2)" by (cases h)
    then show ?case using Cons.IH by (simp add: fold_Some fold_True)
  qed
  have "\<forall>a. (a \<notin> set (map fst xs)) = (a \<notin> set (map fst xs'))"
    using fold_eq fold_None_set
    by metis
  then show ?thesis
    by blast
qed

lemma eq_wset_refl[simp]: "eq_wset xs xs"
  unfolding eq_wset_def
  by simp

lemma eq_wset_sym: "eq_wset xs xs' \<Longrightarrow> eq_wset xs' xs"
  unfolding eq_wset_def
  by fastforce

lemma eq_wset_trans: "eq_wset xs ys \<Longrightarrow> eq_wset ys zs \<Longrightarrow> eq_wset xs zs"
  unfolding eq_wset_def
  by fastforce

lemma eq_wset_elem_switch: "eq_wset (x # x' # xs) (x' # x # xs)"
  unfolding eq_wset_def
  by(auto simp add: add.commute)

lemma eq_wset_elem_comb: "eq_wset ((x,w) # (x,w') # xs) ((x,w + w') # xs)"
  unfolding eq_wset_def
  by(auto simp add: add.commute)

lemma fold_elem_back_aux: "fold (\<lambda>(a, w). (+) (Some w)) (filter (\<lambda>(a', _). a = a') (xs @ e1 # e2 # x's)) w =
         fold (\<lambda>(a, w). (+) (Some w)) (filter (\<lambda>(a', _). a = a') (xs @ e2 # e1 # x's)) w"
  for a :: 'c and e1 e2 :: "'c \<times> ('d :: ab_semigroup_add)" and xs x's :: "('c \<times> 'd) list" and w :: "'d option"
  by(induction xs; (auto simp add: add.assoc[symmetric], simp only: add.commute))

lemma fold_elem_back: "fold (\<lambda>(a, w). (+) (Some w)) (filter (\<lambda>(a', _). a = a') (xs @ e # x's)) w =
        fold (\<lambda>(a, w). (+) (Some w)) (filter (\<lambda>(a', _). a = a') (xs @ x's @ [e])) w"
proof (induction x's arbitrary: xs w)
  case Nil
  show ?case by simp
next
  case (Cons h t)
  from this[of "xs @ [h]" w] show ?case by (subst fold_elem_back_aux) auto
qed

lemma eq_wset_elem_back: "eq_wset (xs @ e # x's) (xs @ x's @ [e])"
  unfolding eq_wset_def
  using fold_elem_back
  by fast

lemma fold_elem_back': "fold (\<lambda>(a, w). (+) (Some w)) (filter (\<lambda>(a', _). a = a') (e # x's)) w =
        fold (\<lambda>(a, w). (+) (Some w)) (filter (\<lambda>(a', _). a = a') (x's @ [e])) w"
  by (metis append_self_conv2 fold_elem_back)

lemma eq_wset_elem_back': "eq_wset (e # x's) (x's @ [e])"
  by (metis eq_wset_def fold_elem_back')

lemma fold_Some_back: "fold (\<lambda>(a, w). (+) (Some w)) (filter (\<lambda>(a', _). a = a') xs) (Some (M :: _ :: ref_ab_semigroup_add)) = sum_key (xs @ [(a, M)]) a"
proof -
  have fold_Some_front: "fold (\<lambda>(a, w). (+) (Some w)) (filter (\<lambda>(a', _). a = a') xs) (Some M) = sum_key ((a, M) # xs) a"
    by simp
  show ?thesis
    using eq_wset_elem_back'
    unfolding eq_wset_def fold_Some_front
    by metis
qed

lemma fold_back': "fold (\<lambda>(a, w). (+) (Some w)) (filter (\<lambda>(a', _). a = a') xs) (Some (M :: _ :: ref_ab_semigroup_add) + w) = fold (\<lambda>(a, w). (+) (Some w)) (filter (\<lambda>(a', _). a = a') (xs @ [(a,M)])) w"
proof -
  have fold_Some_front': "fold (\<lambda>(a, w). (+) (Some w)) (filter (\<lambda>(a', _). a = a') xs) (Some M + w) = fold (\<lambda>(a, w). (+) (Some w)) (filter (\<lambda>(a', _). a = a') ((a,M) # xs)) w"
    by simp
  show ?thesis
    using fold_elem_back'
    unfolding eq_wset_def fold_Some_front'
    by metis
qed

lemma eq_wset_append: "eq_wset xs xs' \<Longrightarrow> eq_wset ys ys' \<Longrightarrow> eq_wset (xs @ ys) (xs' @ ys')"
proof -
  assume H1: "eq_wset xs xs'" and H2: "eq_wset ys ys'"
  have xs_eq: "\<forall>a. sum_key xs a = sum_key xs' a"
    using H1 unfolding eq_wset_def by simp
  have ys_eq: "\<forall>a. sum_key ys a = sum_key ys' a"
    using H2 unfolding eq_wset_def by simp
  show "eq_wset (xs @ ys) (xs' @ ys')"
    unfolding eq_wset_def
  proof (rule allI)
    fix a
    have ha_xs: "sum_key xs a = sum_key xs' a" using xs_eq by simp
    have ha_ys: "sum_key ys a = sum_key ys' a" using ys_eq by simp
    show "sum_key (xs @ ys) a = sum_key (xs' @ ys') a"
    proof (cases "sum_key xs' a")
      case None
      show ?thesis using None ha_xs ha_ys by simp
    next
      case (Some w)
      show ?thesis using Some ha_xs ha_ys by (simp add: fold_Some_back)
    qed
  qed
qed

lemma eq_wset_elem_remove: "eq_wset xs xs' \<Longrightarrow> eq_wset (e # xs) (e # xs')"
  by (metis append_Cons append_Nil eq_wset_refl eq_wset_append)

lemma eq_wset_append_sym: "eq_wset (xs @ ys) (ys @ xs)"
proof (induction xs)
  show "eq_wset ([] @ ys) (ys @ [])"
    by simp
next
  fix a :: "'a \<times> 'b"
    and xs :: "('a \<times> 'b) list"
  assume ind: "eq_wset (xs @ ys) (ys @ xs)"
  have "eq_wset (a # xs @ ys) (xs @ ys @ [a])"
    by (metis append_assoc eq_wset_elem_back')
  also have "eq_wset (ys @ a # xs) (ys @ xs @ [a])"
    by (metis eq_wset_elem_back)
  ultimately have eq_wset_append_sym_aux: "eq_wset (xs @ ys @ [a]) (ys @ xs @ [a]) \<Longrightarrow> eq_wset ((a # xs) @ ys) (ys @ a # xs)"
    by (metis append_Cons eq_wset_trans eq_wset_sym)
  show "eq_wset ((a # xs) @ ys) (ys @ a # xs)"
    using eq_wset_append[OF ind eq_wset_refl[of "[a]"]]
    by (intro eq_wset_append_sym_aux) simp
qed

section \<open>Basic Operations\<close>

lift_definition wempty :: \<open>('a, 'w :: ref_ab_semigroup_add) wset\<close> is
  \<open>[]\<close> .

lift_definition weight :: \<open>('a, 'w :: ref_ab_semigroup_add) wset \<Rightarrow> 'a \<Rightarrow> 'w option\<close> is
  \<open>\<lambda>kxs e. sum_key kxs e\<close>
  unfolding eq_wset_def
  by simp

lemma weight_eq_iff: "(\<forall> x. weight M x = weight N x) = (M = N)"
  using get_abs_wset[of M] get_abs_wset[of N]
  by(auto simp add: weight.abs_eq wset.abs_eq_iff eq_wset_def)

lift_definition wsingle :: \<open>'a \<Rightarrow> 'w \<Rightarrow> ('a, 'w :: ref_ab_semigroup_add) wset\<close> is
  \<open>\<lambda>a w. [(a,w)]\<close> .

lift_definition wset :: \<open>('a, 'w :: ref_ab_semigroup_add) wset \<Rightarrow> 'a set\<close> is
  \<open>\<lambda>M. set (map fst M)\<close> by(drule eq_wset_fst)(auto simp add: image_def)

lift_definition wadd :: \<open>('a, 'w :: ref_ab_semigroup_add) wset \<Rightarrow> ('a, 'w) wset \<Rightarrow> ('a, 'w) wset\<close> is
  \<open>\<lambda>M1 M2. M1 @ M2\<close> using eq_wset_append by metis

lemma sum_key_wupdate_same:
  "sum_key (case w of None \<Rightarrow> filter (\<lambda>(x', _). x \<noteq> x') l
            | Some w' \<Rightarrow> (x, w') # filter (\<lambda>(x', _). x \<noteq> x') l) x = w"
  for l :: "('a \<times> ('w :: ref_ab_semigroup_add)) list"
  by (cases w) (simp_all add: case_prod_beta)

lemma sum_key_wupdate_diff:
  "x \<noteq> x' \<Longrightarrow>
   sum_key (case w of None \<Rightarrow> filter (\<lambda>(x'', _). x \<noteq> x'') l
             | Some w' \<Rightarrow> (x, w') # filter (\<lambda>(x'', _). x \<noteq> x'') l) x' = sum_key l x'"
  for l :: "('a \<times> ('w :: ref_ab_semigroup_add)) list"
proof (cases w)
  case None
  assume neq: "x \<noteq> x'"
  have filter_eq: "filter (\<lambda>y. x \<noteq> fst y \<and> x' = fst y) l = filter (\<lambda>(e', _). x' = e') l \<and>
                   filter (\<lambda>y. x' = fst y \<and> x \<noteq> fst y) l = filter (\<lambda>(e', _). x' = e') l"
    using neq by (auto intro!: filter_cong simp: case_prod_beta)
  then show ?thesis
    unfolding None by (simp add: case_prod_beta filter_eq)
next
  case (Some w')
  assume neq: "x \<noteq> x'"
  have filter_eq: "filter (\<lambda>y. x \<noteq> fst y \<and> x' = fst y) l = filter (\<lambda>(e', _). x' = e') l \<and>
                   filter (\<lambda>y. x' = fst y \<and> x \<noteq> fst y) l = filter (\<lambda>(e', _). x' = e') l"
    using neq by (auto intro!: filter_cong simp: case_prod_beta)
  then show ?thesis
    unfolding Some using neq
    by (simp add: case_prod_beta filter_eq)
qed

lift_definition wupdate :: \<open>('a, 'w :: ref_ab_semigroup_add) wset \<Rightarrow> 'a \<Rightarrow> 'w option \<Rightarrow> ('a, 'w) wset\<close> is
  \<open>\<lambda>M x w. case w of Some w' \<Rightarrow> (x,w') # (filter (\<lambda>(x',_). x \<noteq> x') M) | None \<Rightarrow> filter (\<lambda>(x',_). x \<noteq> x') M\<close>
proof -
  fix l1 l2 :: "('a \<times> ('w :: ref_ab_semigroup_add)) list" and a :: 'a and w :: "'w option"
  assume hyp: "eq_wset l1 l2"
  show "eq_wset (case w of Some w' \<Rightarrow> (a, w') # filter (\<lambda>(x', _). a \<noteq> x') l1
                          | None \<Rightarrow> filter (\<lambda>(x', _). a \<noteq> x') l1)
                (case w of Some w' \<Rightarrow> (a, w') # filter (\<lambda>(x', _). a \<noteq> x') l2
                          | None \<Rightarrow> filter (\<lambda>(x', _). a \<noteq> x') l2)"
    unfolding eq_wset_def
  proof
    fix a'
    show "sum_key (case w of Some w' \<Rightarrow> (a, w') # filter (\<lambda>(x', _). a \<noteq> x') l1
                             | None \<Rightarrow> filter (\<lambda>(x', _). a \<noteq> x') l1) a' =
          sum_key (case w of Some w' \<Rightarrow> (a, w') # filter (\<lambda>(x', _). a \<noteq> x') l2
                             | None \<Rightarrow> filter (\<lambda>(x', _). a \<noteq> x') l2) a'"
    proof (cases "a = a'")
      case True
      then show ?thesis by (simp only: True sum_key_wupdate_same)
    next
      case False
      with hyp show ?thesis
        unfolding eq_wset_def
        by (simp add: sum_key_wupdate_diff)
    qed
  qed
qed

instantiation wset :: (type, type) size
begin

definition size_wset where
  size_wset_overloaded_def: "size_wset M = card (wset M)"
instance ..

end

lemma weight_wsingle[simp] : "weight (wsingle x w) x' = (if x = x' then Some w else None)"
  by transfer simp

lemma sum_key_append_aux:
  "sum_key (l1 @ l2) x = sum_key l1 x + sum_key l2 x"
  for l1 l2 :: "('a \<times> ('w :: ref_ab_semigroup_add)) list"
  by (induction l1) (auto simp add: fold_Some_back fold_back' add.assoc)

lemma weight_add[simp] : "weight (wadd M1 M2) x = weight M1 x + weight M2 x"
  by transfer (rule sum_key_append_aux)

lemma weight_wempty[simp] : "weight wempty = (\<lambda>_ . None)"
  by transfer simp

lemma weight_wupdate[simp] : "weight (wupdate M x w) = (weight M)(x := w)"
proof -
  have H1: "weight (wupdate M x w) x = w"
    by transfer (rule sum_key_wupdate_same)
  have H2: "x \<noteq> x' \<Longrightarrow> weight (wupdate M x w) x' = weight M x'" for x'
    by transfer (rule sum_key_wupdate_diff)
  show ?thesis
  proof (rule ext)
    fix x'
    show "weight (wupdate M x w) x' = ((weight M)(x := w)) x'"
    proof (cases "x = x'")
      case True
      then show ?thesis using H1 by simp
    next
      case False
      then show ?thesis using H2[OF False] by simp
    qed
  qed
qed

lemma wupdate_wupdate[simp]: "wupdate (wupdate M x w) x w' = wupdate M x w'"
  by(simp add: weight_eq_iff[symmetric])

section \<open>The Splitting Relation\<close>

abbreviation fold' where
  "fold' l \<equiv> foldl (+) (hd l) (tl l)"

inductive list_split :: "('a\<times>'w :: ref_ab_semigroup_add) list \<Rightarrow> ('a\<times>'w) list \<Rightarrow> bool" where
  Base: "list_split [] []"
| Split: "list_split xs'' ys \<Longrightarrow> xs = xs' @ xs'' \<Longrightarrow> w = fold' (map snd xs') \<Longrightarrow> xs' \<noteq> [] \<Longrightarrow> list_all (\<lambda>(a,b). a = y) xs' \<Longrightarrow> list_split xs ((y,w) # ys)"

inductive list_split' :: "((('w :: ref_ab_semigroup_add) option) list) list \<Rightarrow> ('w option) list \<Rightarrow> bool" where
  Base': "list_split' [] []"
| Split': "list_split' xss ys \<Longrightarrow> y = fold' xs \<Longrightarrow> xs \<noteq> [] \<Longrightarrow> list_split' (xs # xss) (y # ys)"


lemma list_split_cons_eq: "list_split xs1 xs2 \<Longrightarrow> list_split (x # xs1) (x # xs2)"
proof (cases x)
  case (Pair x1 w)
  assume H: "list_split xs1 xs2"
  show ?thesis
    unfolding Pair
    by (rule Split[where xs'' = xs1 and ys = xs2 and xs' = "[(x1, w)]" and y = x1 and w = w])
      (use H in simp_all)
qed

lemma list_split_refl[simp]: "list_split xs xs"
proof (induction xs)
  case Nil
  show ?case by (subst list_split.simps; simp)
next
  case (Cons x xs')
  show ?case by (rule list_split_cons_eq; simp add: Cons.IH)
qed

lemma list_split_comb: "list_split ((x, w) # (x, w') # xs) ((x, w + w') # xs)"
proof (rule Split[where xs'' = xs and ys = xs and xs' = "[(x, w), (x, w')]" and y = x and w = "w + w'"])
  show "list_split xs xs" by simp
  show "(x, w) # (x, w') # xs = [(x, w), (x, w')] @ xs" by simp
  show "w + w' = fold' (map snd [(x, w), (x, w')])" by simp
  show "[(x, w), (x, w')] \<noteq> []" by simp
  show "list_all (\<lambda>(a, b). a = x) [(x, w), (x, w')]" by simp
qed

lemma list_split_nil[simp]: "list_split xs [] = (xs = [])" "list_split [] xs = (xs = [])"
  by(subst list_split.simps; simp)+

lemma eq_wset_nil[simp]: "eq_wset xs [] = (xs = [])"
proof (cases xs)
  case Nil
  then show ?thesis by simp
next
  case (Cons x w)
  then show ?thesis
  proof (cases x)
    case (Pair a b)
    then show ?thesis using Cons by (auto simp add: eq_wset_def fold_Some')
  qed
qed

lemma list_split_eq_wset:
  assumes A: "list_split xs ys"
  shows "eq_wset xs ys"
proof -
  have H1: "xs \<noteq> [] \<Longrightarrow> list_all (\<lambda>(a, b). a = x) xs \<Longrightarrow> eq_wset ((x, w) # xs) [(x, foldl (+) w (map snd xs))]" for x :: 'a and xs :: "('a \<times> ('w :: ref_ab_semigroup_add)) list" and w :: 'w
  proof (induction xs arbitrary: w)
    case Nil
    then show ?case
      unfolding eq_wset_def
      by simp
  next
    case (Cons x' xs' w)
    then show ?case
      by (cases x'; cases xs'; simp add: eq_wset_trans[OF eq_wset_elem_comb])
  qed
  have H2: "xs \<noteq> [] \<Longrightarrow> list_all (\<lambda>(a, b). a = y) xs \<Longrightarrow> eq_wset xs [(y, fold' (map snd xs))]" for xs :: "('a \<times> ('w :: ref_ab_semigroup_add)) list" and y :: 'a
  proof (induction xs)
    case Nil
    then show ?case by simp
  next
    case (Cons x xs')
    then show ?case
    proof (cases x)
      case (Pair a w)
      show ?thesis
      proof (cases xs')
        case Nil
        then show ?thesis using Cons Pair by simp
      next
        case (Cons x' xs'')
        have xs'_ne: "xs' \<noteq> []" using Cons by simp
        have all_xs': "list_all (\<lambda>(a, b). a = y) xs'" using Cons.prems by simp
        have a_y: "a = y" using Cons.prems Pair by simp
        have "eq_wset ((y, w) # xs') [(y, foldl (+) w (map snd xs'))]"
          using H1[OF xs'_ne all_xs'] .
        then show ?thesis using Pair a_y by simp
      qed
    qed
  qed
  from A show ?thesis
  proof (induction rule: list_split.induct)
    case Base
    then show ?case by simp
  next
    case (Split xs'' ys xs xs' w y)
    have eq_tail: "eq_wset xs'' ys" using Split.IH .
    have eq_head: "eq_wset xs' [(y, fold' (map snd xs'))]"
      using H2 Split.hyps(4) Split.hyps(5) by blast
    have "eq_wset (xs' @ xs'') ([(y, fold' (map snd xs'))] @ ys)"
      using eq_head eq_tail by (rule eq_wset_append)
    then show ?case using Split.hyps(2) Split.hyps(3) by simp
  qed
qed


lemma list_split_app: "list_split xs (ys @ ys') \<Longrightarrow> \<exists> xs' xs''. list_split xs' ys \<and> list_split xs'' ys' \<and> xs = xs' @ xs''"
proof (induction ys arbitrary: xs)
  case Nil
  then show ?case by auto
next
  case (Cons y yss)
  obtain a w where y_def: "y = (a, w)" by (cases y)
  from Cons.prems have split_y: "list_split xs ((a, w) # (yss @ ys'))"
    unfolding y_def by simp
  then obtain xs1 xs2 where
    xs_def: "xs = xs1 @ xs2"
    and split_tail: "list_split xs2 (yss @ ys')"
    and w_def: "w = fold' (map snd xs1)"
    and xs1_ne: "xs1 \<noteq> []"
    and xs1_all: "list_all (\<lambda>(a', b). a' = a) xs1"
    by (auto elim: list_split.cases)
  from Cons.IH[OF split_tail] obtain xs' xs'' where
    split_l: "list_split xs' yss"
    and split_r: "list_split xs'' ys'"
    and xs2_def: "xs2 = xs' @ xs''"
    by blast
  have split_left: "list_split (xs1 @ xs') ((a, w) # yss)"
    using split_l w_def xs1_ne xs1_all by (intro Split) simp_all
  show ?case
    unfolding y_def
    using split_left split_r xs_def xs2_def by auto
qed

lemma list_split_trans: 
  assumes H:"list_split xs ys"
    and H1: "list_split ys zs"
  shows "list_split xs zs"
proof -
  have H2': "list_all (\<lambda>(a, b). a = e) xs \<Longrightarrow> \<forall> e'. filter (\<lambda>(a', _). e' = a') xs = (if e = e' then xs else [])" for e :: 'a and xs :: "('a \<times> 'w) list"
  proof (induction xs)
    case Nil
    then show ?case by simp
  next
    case (Cons x xs')
    then show ?case by (cases x) auto
  qed
  have fold_upd: "fold (\<lambda>(a, w). (+) (Some w)) (if e = fst y then y # filter (\<lambda>(a', _). e = a') ys else filter (\<lambda>(a', _). e = a') ys) (ws e) = 
        fold (\<lambda>(a, w). (+) (Some w)) (filter (\<lambda>(a', _). e = a') ys) ((ws(fst y:= Some (snd y) + ws (fst y))) e)" for e :: 'a and ws :: "'a \<Rightarrow> ('w :: ref_ab_semigroup_add) option" and ys :: "('a \<times> 'w) list" and y :: "('a \<times> 'w)"
  proof (cases y)
    case (Pair a w)
    then show ?thesis by (cases "e = a") simp_all
  qed
  have list_all_eq_aux: "list_all (\<lambda>(a, b). a = e) xs \<Longrightarrow>
    \<forall>a. fold (\<lambda>(a, w). (+) (Some w)) (if e = a then xs else []) None = fold (\<lambda>(a, w). (+) (Some w)) (filter (\<lambda>(a', _). a = a') ys) (w a) \<Longrightarrow> list_all (\<lambda>(a, b). a = e) ys" for e :: 'a and xs :: "('a \<times> ('w :: ref_ab_semigroup_add)) list" and ys :: "('a \<times> 'w) list" and w :: "'a \<Rightarrow> 'w option"
  proof (induction ys arbitrary: w)
    case Nil
    then show ?case by (simp add: case_prod_beta)
  next
    case (Cons y ys')
    assume all_xs: "list_all (\<lambda>(a, b). a = e) xs"
    assume hall: "\<forall>a. fold (\<lambda>(a, w). (+) (Some w)) (if e = a then xs else []) None =
                      fold (\<lambda>(a, w). (+) (Some w)) (filter (\<lambda>(a', _). a = a') (y # ys')) (w a)"
    have hall': "\<forall>a. fold (\<lambda>(a, w). (+) (Some w)) (if e = a then xs else []) None =
                     fold (\<lambda>(a, w). (+) (Some w)) (filter (\<lambda>(a', _). a = a') ys') 
                          ((w(fst y := Some (snd y) + w (fst y))) a)"
      using hall by (simp add: fold_upd[of _ _ _ w] case_prod_beta)
    have ys'_all: "list_all (\<lambda>(a, b). a = e) ys'"
      using Cons.IH[of "w(fst y := Some (snd y) + w (fst y))"] all_xs hall' by fast
    have y_eq: "fst y = e"
    proof (rule ccontr)
      assume ne: "fst y \<noteq> e"
      have h_fy: "fold (\<lambda>(a, w). (+) (Some w)) (if e = fst y then xs else []) None =
                  fold (\<lambda>(a, w). (+) (Some w)) (filter (\<lambda>(a', _). fst y = a') (y # ys')) (w (fst y))"
        using hall[THEN spec, of "fst y"] by simp
      have lhs: "fold (\<lambda>(a, w). (+) (Some w)) (if e = fst y then xs else []) None = None"
        using ne by simp
      have rhs_pos: "fold (\<lambda>(a, w). (+) (Some w)) (filter (\<lambda>(a', _). fst y = a') (y # ys')) (w (fst y)) \<noteq> None"
        by (simp add: H2'[OF all_xs] H2' plus_option_case case_prod_beta fold_Some
            split: if_splits)
      then show False using lhs h_fy by simp
    qed
    show "list_all (\<lambda>(a, b). a = e) (y # ys')"
      using y_eq ys'_all by (cases y) auto
  qed
  have list_all_eq_wset: "list_all (\<lambda>(a, b). a = e) xs \<Longrightarrow> eq_wset xs ys \<Longrightarrow> list_all (\<lambda>(a, b). a = e) ys" for e :: 'a and xs :: "('a \<times> ('w :: ref_ab_semigroup_add)) list" and ys :: "('a \<times> 'w) list"
    unfolding eq_wset_def
    by(simp add: H2' list_all_eq_aux[of e xs ys "\<lambda>_. None"])
  have fold_Some_eq: "fold (\<lambda>(a, w). (+) (Some w)) ys (Some wy) = fold (\<lambda>(a, w). (+) (Some w)) xs (Some wx) \<Longrightarrow>
               fold (\<lambda>x s. s + x) (map snd xs) wx = fold (\<lambda>x s. s + x) (map snd ys) wy" for xs :: "('a \<times> ('w :: ref_ab_semigroup_add)) list" and ys :: "('a \<times> 'w) list" and wx :: 'w and wy :: 'w
  proof (induction xs arbitrary: wx)
    case (Nil wx)
    then show ?case
    proof (induction ys arbitrary: wy)
      case Nil
      then show ?case by simp
    next
      case (Cons h t)
      then show ?case by (simp add: plus_option_case case_prod_beta ab_semigroup_add_class.add.commute)
    qed
  next
    case (Cons x xs' wx)
    then show ?case by (simp add: case_prod_beta ab_semigroup_add_class.add.commute)
  qed
  have fold_hd_tl_eq: "xs \<noteq> [] \<Longrightarrow>
    fold (\<lambda>(a, w). (+) (Some w)) ys None = fold (\<lambda>(a, w). (+) (Some w)) xs None \<Longrightarrow>
    fold (\<lambda>x s. s + x) (tl (map snd xs)) (hd (map snd xs)) = fold (\<lambda>x s. s + x) (tl (map snd ys)) (hd (map snd ys))" for xs :: "('a \<times> ('w :: ref_ab_semigroup_add)) list" and ys :: "('a \<times> 'w) list"
  proof -
    assume ne: "xs \<noteq> []"
    assume feq: "fold (\<lambda>(a, w). (+) (Some w)) ys None = fold (\<lambda>(a, w). (+) (Some w)) xs None"
    show "fold (\<lambda>x s. s + x) (tl (map snd xs)) (hd (map snd xs)) = fold (\<lambda>x s. s + x) (tl (map snd ys)) (hd (map snd ys))"
    proof (cases xs)
      case Nil
      then show ?thesis using ne by simp
    next
      case (Cons x xs')
      then show ?thesis
      proof (cases ys)
        case Nil
        then show ?thesis using \<open>xs = x # xs'\<close> feq by (cases x; simp add: fold_Some)
      next
        case (Cons y ys')
        then show ?thesis using \<open>xs = x # xs'\<close> feq by (auto simp add: case_prod_beta intro: fold_Some_eq)
      qed
    qed
  qed
  have H2: "xs \<noteq> [] \<Longrightarrow>
    list_all (\<lambda>(a, b). a = e) xs \<Longrightarrow>
    eq_wset ys xs \<Longrightarrow> fold' (map snd xs) = fold' (map snd ys) \<and> ys \<noteq> [] \<and> list_all (\<lambda>(a, b). a = e) ys" for xs :: "('a \<times> ('w :: ref_ab_semigroup_add)) list" and ys :: "('a \<times> 'w) list" and e :: 'a
  proof -
    assume ne: "xs \<noteq> []"
    assume all_xs: "list_all (\<lambda>(a, b). a = e) xs"
    assume eq: "eq_wset ys xs"
    have all_ys: "list_all (\<lambda>(a, b). a = e) ys"
      using list_all_eq_wset[OF all_xs, OF eq_wset_sym[OF eq]] .
    have ys_ne: "ys \<noteq> []"
    proof -
      obtain a w xs' where xs_eq: "xs = (a, w) # xs'"
        using ne by (cases xs) auto
      have a_eq: "a = e"
        using all_xs xs_eq by simp
      have xs_pos: "sum_key xs e \<noteq> None"
        by (simp add: xs_eq a_eq case_prod_beta fold_Some H2'[OF all_xs])
      have eq_e: "sum_key ys e = sum_key xs e"
        using eq unfolding eq_wset_def by simp
      show ?thesis
        using all_ys eq_e xs_pos by (auto simp add: fold_Some)
    qed
    have fold_eq: "fold' (map snd xs) = fold' (map snd ys)"
    proof -
      have xs_e: "sum_key xs e = fold (\<lambda>(a, w). (+) (Some w)) xs None"
        by (simp add: H2'[OF all_xs])
      have ys_e: "sum_key ys e = fold (\<lambda>(a, w). (+) (Some w)) ys None"
        by (simp add: H2'[OF all_ys])
      have key: "fold (\<lambda>(a, w). (+) (Some w)) ys None = fold (\<lambda>(a, w). (+) (Some w)) xs None"
        using eq xs_e ys_e unfolding eq_wset_def by simp
      show ?thesis
        using fold_hd_tl_eq[OF ne, OF key] ne ys_ne by (simp add: foldl_conv_fold)
    qed
    show "fold' (map snd xs) = fold' (map snd ys) \<and> ys \<noteq> [] \<and> list_all (\<lambda>(a, b). a = e) ys"
      using fold_eq ys_ne all_ys by simp
  qed
  show ?thesis
    using H1 H
  proof (induction ys zs arbitrary: xs rule: list_split.induct)
    case (Base xs)
    then show ?case by simp
  next
    case (Split xs'' ys' xs' zs1' w y xs)
    from Split.prems Split.hyps(2) have split_app: "list_split xs (zs1' @ xs'')"
      by simp
    from list_split_app[OF split_app] obtain xs_a xs_b where
      xs_split: "xs = xs_a @ xs_b"
      and split_a: "list_split xs_a zs1'"
      and split_b: "list_split xs_b xs''"
      by blast
    have eq_a: "eq_wset xs_a zs1'"
      using list_split_eq_wset[OF split_a] .
    have props_a: "fold' (map snd zs1') = fold' (map snd xs_a) \<and> xs_a \<noteq> [] \<and> list_all (\<lambda>(a, b). a = y) xs_a"
      using H2[OF Split.hyps(4) Split.hyps(5) eq_a] .
    have xs_a_ne: "xs_a \<noteq> []" using props_a by blast
    have xs_a_all: "list_all (\<lambda>(a, b). a = y) xs_a" using props_a by blast
    have w_xs_a: "w = fold' (map snd xs_a)"
      using Split.hyps(3) props_a by simp
    have split_b': "list_split xs_b ys'"
      using Split.IH[OF split_b] .
    show ?case
      unfolding xs_split
      by (intro list_split.Split[OF split_b' _ w_xs_a xs_a_ne xs_a_all])
        simp
  qed
qed

lemma list_split'_length: "list_split' xs ys \<Longrightarrow> length xs = length ys"
  by (induction xs arbitrary: ys) (auto elim: list_split'.cases)

lemma foldl_assoc: "(\<And>a b c. f (f a b) c = f a  (f b c)) \<Longrightarrow> f z (foldl f y xs) = foldl f (f z y) xs"
  by (induction xs arbitrary: z y) auto

lemma list_split'_refl: "list_split' (map (\<lambda>x. [x]) xs) xs"
  by (induction xs) (auto intro: list_split'.intros)

fun option_list :: "('a option) list \<Rightarrow> 'a list" where
  "option_list [] = []" |
  "option_list (None # l) = option_list l" |
  "option_list (Some a # l) = a # option_list l"

lemma option_list_eq_filter: "filter ((\<noteq>) None) l1 = filter ((\<noteq>) None) l2 \<Longrightarrow> option_list l1 = option_list l2"
proof (induction "length l1 + length l2" arbitrary: l1 l2)
  fix l1 :: "'b option list"
    and l2 :: "'b option list"
  assume "0 = length (l1::'b option list) + length (l2::'b option list)"
    and "filter ((\<noteq>) None) l1 = filter ((\<noteq>) None) l2"
  then show "(option_list l1::'b list) = option_list l2"
    by simp
next
  fix x :: nat
    and l1 :: "'b option list"
    and l2 :: "'b option list"
  assume ind: "\<And>(l1 :: 'b option list) l2. x = length l1 + length l2 \<Longrightarrow> filter ((\<noteq>) None) l1 = filter ((\<noteq>) None) l2 \<Longrightarrow> option_list l1 = option_list l2"
    and len: "Suc x = length (l1::'b option list) + length (l2::'b option list)"
    and eq_l: "filter ((\<noteq>) None) l1 = filter ((\<noteq>) None) l2"
  consider "l1 = [] \<or> l2 = []" | "l1 \<noteq> [] \<and> l2 \<noteq> []"
    by auto
  then show "(option_list l1::'b list) = option_list l2"
  proof (cases, goal_cases "eq" "noteq")
    case eq
    then show ?case
    proof (cases "l1 = []")
      case True
      show ?thesis
      proof (cases l2)
        case Nil
        then show ?thesis using True by simp
      next
        case (Cons h2 t2)
        then show ?thesis
        proof (cases h2)
          case None
          then show ?thesis using True Cons ind[of l1 t2] len eq_l by simp
        next
          case (Some v)
          then show ?thesis using True Cons eq_l by simp
        qed
      qed
    next
      case False
      with eq have "l2 = []" by simp
      show ?thesis
      proof (cases l1)
        case Nil
        then show ?thesis using False by simp
      next
        case (Cons h1 t1)
        then show ?thesis
        proof (cases h1)
          case None
          then show ?thesis using \<open>l2 = []\<close> Cons ind[of t1 l2] len eq_l by simp
        next
          case (Some v)
          then show ?thesis using False \<open>l2 = []\<close> Cons eq_l by simp
        qed
      qed
    qed
  next
    case noteq
    then show ?case
    proof (cases l1)
      case Nil
      then show ?thesis using noteq by simp
    next
      case (Cons h1 t1)
      show ?thesis
      proof (cases l2)
        case Nil
        then show ?thesis using noteq by simp
      next
        case (Cons h2 t2)
        then show ?thesis
        proof (cases h1)
          case None
          then show ?thesis using \<open>l1 = h1 # t1\<close> Cons ind[of t1 l2] len eq_l by simp
        next
          case (Some v1)
          then show ?thesis
          proof (cases h2)
            case None
            then show ?thesis using \<open>l1 = h1 # t1\<close> Cons \<open>h1 = Some v1\<close> ind[of l1 t2] len eq_l by simp
          next
            case (Some v2)
            then show ?thesis using \<open>l1 = h1 # t1\<close> Cons \<open>h1 = Some v1\<close> ind[of t1 "None # t2"] len eq_l by simp
          qed
        qed
      qed
    qed
  qed
qed



lemma fold_option_not_none: "Some a = fold' l \<Longrightarrow> l \<noteq> [] \<Longrightarrow> (option_list l) \<noteq> []"
proof (induction l arbitrary: a)
  case Nil
  then show ?case by simp
next
  case (Cons h t)
  then show ?case by (cases h; cases t) auto
qed


lemma fold_option: "Some a = fold' l \<Longrightarrow> l \<noteq> [] \<Longrightarrow> a = fold' (option_list l)"
proof -
  have H: "Some x = foldl (+) (Some x') l \<Longrightarrow> x = foldl (+) x' (option_list l)"
    for x x' and l :: "'a option list"
  proof (induction l arbitrary: x x')
    case Nil
    then show ?case by simp
  next
    case (Cons a l)
    then show ?case by (cases a) (auto simp add: plus_option_def split: option.split)
  qed
  show "Some a = fold' l \<Longrightarrow> l \<noteq> [] \<Longrightarrow> a = fold' (option_list l)"
  proof (induction l arbitrary: a)
    case Nil
    then show ?case by simp
  next
    case (Cons h t)
    then show ?case
    proof (cases h)
      case None
      then show ?thesis using Cons by (cases t) auto
    next
      case (Some a')
      then show ?thesis using H[of a a' t] Cons by simp
    qed
  qed
qed

fun create_split :: "('a \<times> 'w) list \<Rightarrow> ('a \<Rightarrow> (('w option) list) list) \<Rightarrow> ('a \<times> 'w) list" where
  "create_split [] als = []" |
  "create_split ((a,_) # l) als =  map (\<lambda>x. (a,x)) (option_list (hd (als a))) @ (create_split l (als(a := tl(als a))))"

lemma list_split'_exist: 
  "((xs \<noteq> [] \<and> ys \<noteq> []) \<longrightarrow> fold' (xs :: (('w :: ref_ab_semigroup_add) option) list) = fold' ys) \<Longrightarrow>
    ((xs = []) = (ys = [])) \<Longrightarrow>
  (\<exists>zs zs'. list_split' zs xs \<and> list_split' zs' ys \<and> (\<forall>n m. n < length xs \<longrightarrow> m < length ys \<longrightarrow> zs ! n ! m = zs' ! m ! n) \<and> 
    list_all (\<lambda>l. length l = length ys) zs \<and> list_all (\<lambda>l. length l = length xs) zs')"
proof (induction "length xs + length ys" arbitrary: xs ys rule: nat_less_induct)
  fix xs :: "('w option) list"
    and ys :: "('w option) list"
  assume ind: "\<forall>m<length (xs :: (('w :: ref_ab_semigroup_add) option) list) + length ys.
          \<forall>(x :: (('w :: ref_ab_semigroup_add) option) list) ls'.
             m = length x + length ls' \<longrightarrow>
             (x \<noteq> [] \<and> ls' \<noteq> [] \<longrightarrow> fold' x = fold' ls') \<longrightarrow>
             (x = []) = (ls' = []) \<longrightarrow>
             (\<exists>zs zs'.
                 list_split' zs x \<and> list_split' zs' ls' \<and> (\<forall>n m. n < length x \<longrightarrow> m < length ls' \<longrightarrow> zs ! n ! m = zs' ! m ! n) \<and> list_all (\<lambda>l. length l = length ls') zs \<and> list_all (\<lambda>l. length l = length x) zs')"
    and eq_app: "(xs \<noteq> [] \<and> ys \<noteq> []) \<longrightarrow> fold' (xs :: (('w :: ref_ab_semigroup_add) option) list) = fold' ys"
    and eq_nil: "(xs = []) = (ys = [])"
  have ind: "\<And>(x :: (('w :: ref_ab_semigroup_add) option) list) ls'.
             length x + length ls' < length xs + length ys \<Longrightarrow>
             (x \<noteq> [] \<and> ls' \<noteq> [] \<longrightarrow> fold' x = fold' ls') \<Longrightarrow>
             (x = []) = (ls' = []) \<Longrightarrow>
             (\<exists>zs zs'.
                 list_split' zs x \<and> list_split' zs' ls' \<and> (\<forall>n m. n < length x \<longrightarrow> m < length ls' \<longrightarrow> zs ! n ! m = zs' ! m ! n) \<and> list_all (\<lambda>l. length l = length ls') zs \<and> list_all (\<lambda>l. length l = length x) zs')"
    using ind by auto
  have gt3_cases: "\<And>(xs :: 'w option list) ys. ((xs = []) = (ys = [])) \<Longrightarrow>
            ((xs \<noteq> [] \<and> ys \<noteq> []) \<longrightarrow> fold' (xs :: (('w :: ref_ab_semigroup_add) option) list) = fold' ys) \<Longrightarrow>
            (\<And>(x :: (('w :: ref_ab_semigroup_add) option) list) ls'.
             length x + length ls' < length xs + length ys \<Longrightarrow>
             (x \<noteq> [] \<and> ls' \<noteq> [] \<longrightarrow> fold' x = fold' ls') \<Longrightarrow>
             (x = []) = (ls' = []) \<Longrightarrow>
             (\<exists>zs zs'.
                 list_split' zs x \<and> list_split' zs' ls' \<and> (\<forall>n m. n < length x \<longrightarrow> m < length ls' \<longrightarrow> zs ! n ! m = zs' ! m ! n) \<and> list_all (\<lambda>l. length l = length ls') zs \<and> list_all (\<lambda>l. length l = length x) zs')) \<Longrightarrow>
2 < length xs \<Longrightarrow> \<exists>zs zs'.
       list_split' zs xs \<and>
       list_split' zs' ys \<and>
       (\<forall>n m. n < length xs \<longrightarrow> m < length ys \<longrightarrow> zs ! n ! m = zs' ! m ! n) \<and>
       list_all (\<lambda>l. length l = length ys) zs \<and> list_all (\<lambda>l. length l = length xs) zs'"
  proof -
    fix xs :: "'w option list" and ys :: "'w option list"
    assume len: "2 < length xs"
      and eq_nil: "(xs = []) = (ys = [])"
      and eq_app: "(xs \<noteq> [] \<and> ys \<noteq> []) \<longrightarrow> fold' (xs :: (('w :: ref_ab_semigroup_add) option) list) = fold' ys"
      and ind: "\<And>(x :: (('w :: ref_ab_semigroup_add) option) list) ls'.
           length x + length ls' < length xs + length ys \<Longrightarrow>
           (x \<noteq> [] \<and> ls' \<noteq> [] \<longrightarrow> fold' x = fold' ls') \<Longrightarrow>
           (x = []) = (ls' = []) \<Longrightarrow>
           (\<exists>zs zs'.
               list_split' zs x \<and> list_split' zs' ls' \<and> (\<forall>n m. n < length x \<longrightarrow> m < length ls' \<longrightarrow> zs ! n ! m = zs' ! m ! n) \<and> list_all (\<lambda>l. length l = length ls') zs \<and> list_all (\<lambda>l. length l = length x) zs')"
    obtain x x' xs' where xs_def: "xs = x # x' # xs'" and xs'_nil: "xs' \<noteq> []"
      using len
      by (metis One_nat_def Suc_1 Suc_eq_plus1 length_0_conv length_Cons less_nat_zero_code list.exhaust not_add_less1 verit_comp_simplify1(1))
    have "\<exists> zs zs'. list_split' zs ((x + x') # xs') \<and>
       list_split' zs' ys \<and>
       (\<forall>n m. n < length ((x + x') # xs') \<longrightarrow> m < length ys \<longrightarrow> zs ! n ! m = zs' ! m ! n) \<and>
       list_all (\<lambda>l. length l = length ys) zs \<and> list_all (\<lambda>l. length l = length ((x + x') # xs')) zs'"
      using ind[of "(x + x') # xs'" ys] eq_app eq_nil
      unfolding xs_def
      by auto
    obtain zs zs' where ind1: "list_split' zs ((x + x') # xs') \<and>
       list_split' zs' ys \<and>
       (\<forall>n m. n < length ((x + x') # xs') \<longrightarrow> m < length ys \<longrightarrow> zs ! n ! m = zs' ! m ! n) \<and>
       list_all (\<lambda>l. length l = length ys) zs \<and> list_all (\<lambda>l. length l = length ((x + x') # xs')) zs'"
      using ind[of "(x + x') # xs'" ys] eq_app eq_nil
      unfolding xs_def
      by auto
    have "\<exists>zsa zs'.
     list_split' zsa [x, x'] \<and>
     list_split' zs' (hd zs) \<and>
     (\<forall>n m. n < length [x, x'] \<longrightarrow> m < length (hd zs) \<longrightarrow> zsa ! n ! m = zs' ! m ! n) \<and> list_all (\<lambda>l. length l = length (hd zs)) zsa \<and> list_all (\<lambda>l. length l = length [x, x']) zs'"
    proof (rule ind[of "[x, x']" "hd zs"])
      show "length [x, x'] + length (hd zs) < length xs + length ys"
        using len eq_nil ind1
        by (cases zs) (auto elim: list_split'.cases simp add: less_eq_Suc_le)
      show "[x, x'] \<noteq> [] \<and> hd zs \<noteq> [] \<longrightarrow> fold' [x, x'] = fold' (hd zs)"
        using len eq_nil ind1
        by (auto elim: list_split'.cases simp add: ab_semigroup_add_class.add.commute)
      show "([x, x'] = []) = (hd zs = [])"
        using len eq_nil ind1
        by (auto elim: list_split'.cases simp add: ab_semigroup_add_class.add.commute)
    qed
    then obtain zs1 zs1' where ind2: "list_split' zs1 [x, x'] \<and> list_split' zs1' (hd zs) \<and>
     (\<forall>n m. n < length [x, x'] \<longrightarrow> m < length (hd zs) \<longrightarrow> zs1 ! n ! m = zs1' ! m ! n) \<and> list_all (\<lambda>l. length l = length (hd zs)) zs1 \<and> list_all (\<lambda>l. length l = length [x, x']) zs1'"
      by blast
    have H1: "list_split' (zs1 ! 0 # zs1 ! 1 # tl zs) xs"
    proof (cases zs1)
      case Nil
      then show ?thesis using ind1 ind2 unfolding xs_def by (auto elim: list_split'.cases)
    next
      case (Cons e zss1)
      then show ?thesis using ind1 ind2 unfolding xs_def
        by (cases zss1) (auto intro!: list_split'.intros elim: list_split'.cases)
    qed
    have "\<And>m n. m < length ys \<longrightarrow> zs ! 0 ! m = zs' ! m ! 0" "list_split' zs' ys" "list_split' zs1' (hd zs)" "list_all (\<lambda>l. length l = length [x, x']) zs1'" "list_all (\<lambda>l. length l = length ys) zs"
      using ind1 ind2 by auto
    also have len_zs1': "length zs1' = length ys" 
      using ind1 ind2 list_split'_length
      by (metis (mono_tags, lifting) hd_conv_nth length_greater_0_conv list.distinct(1) list_all_length)
    moreover have "ys \<noteq> [] \<Longrightarrow> zs \<noteq> []"
      using ind1 
      by (auto elim: list_split'.cases)
    ultimately have H2: "list_split' (map2 (\<lambda>l l'. (l' ! 0) # (l' ! 1) # (tl l)) zs' zs1') ys"
    proof (induction ys arbitrary: zs zs' zs1')
      case Nil
      then show ?case
        by(auto intro: list_split'.intros dest: list_split'.cases)
    next
      fix y :: "'w option"
        and ys :: "'w option list"
        and zs :: "'w option list list"
        and zs' :: "'w option list list"
        and zs1' :: "'w option list list"
      assume ind: "\<And>zs zs' zs1'. (\<And>m. m < length ys \<longrightarrow> zs ! 0 ! m = zs' ! m ! 0) \<Longrightarrow> list_split' zs' ys \<Longrightarrow> list_split' zs1' (hd zs) \<Longrightarrow> list_all (\<lambda>l. length l = length [x, x']) zs1' \<Longrightarrow> list_all (\<lambda>l. length l = length ys) zs  \<Longrightarrow> length zs1' = length ys \<Longrightarrow> (ys \<noteq> [] \<Longrightarrow> zs \<noteq> []) \<Longrightarrow> list_split' (map2 (\<lambda>x y. y ! 0 # y ! 1 # tl x) zs' zs1') ys"
        and trans: "\<And>m. m < length (y # ys) \<longrightarrow> (zs ! 0 ! m::'w option) = zs' ! m ! 0"
        and zs'_ys: "list_split' zs' (y # ys)"
        and zs1'_zs: "list_split' zs1' (hd zs::'w option list)"
        and len: "list_all (\<lambda>l. length (l::'w option list) = length [x, x']) zs1'"
        and len_zs: "list_all (\<lambda>l. length l = length (y # ys)) zs"
        and len': "length zs1' = length (y # ys)"
        and zs_Nil: "(y # ys) \<noteq> [] \<Longrightarrow> zs \<noteq> []"
      have trans': "zs ! 0 ! 0 = zs' ! 0 ! 0"
        using trans by auto
      have zs_Nil: "zs \<noteq> []"
        using zs_Nil by simp
      obtain z zss' where zs'_def: "zs' = z # zss'" and y_fold: "y = fold' z" and zss'_ys: "list_split' zss' ys" and z_Nil: "z \<noteq> []"
        using zs'_ys
        by(auto elim: list_split'.cases)
      obtain ze zl where z_app: "z = ze # zl"
        using z_Nil 
        by (meson list.exhaust)
      have ze_def: "ze = zs ! 0 ! 0"
        using trans'
        unfolding zs'_def z_app
        by simp
      obtain zse zsl where zs_def: "zs = zse # zsl"
        using zs_Nil
        using list.exhaust by auto
      have exist_zs1': "\<exists> zs1'e1 zs1'e2 zs1'l. zs1' = [zs1'e1, zs1'e2] # zs1'l \<and> zs1'e1 + zs1'e2 = ze"
      proof (cases rule: list_split'.cases[OF zs1'_zs])
        case 1
        then show ?thesis using len' zs1'_zs by auto
      next
        case (2 xss ys' y xs)
        then show ?thesis
          using len ze_def zs_def
          by (cases xs; cases "tl xs") auto
      qed
      then obtain zs1'e1 zs1'e2 zs1'l where zs1'_def: "zs1' = [zs1'e1, zs1'e2] # zs1'l \<and> zs1'e1 + zs1'e2 = ze"
        by auto
      show "list_split' (map2 (\<lambda>x y. y ! 0 # y ! 1 # tl x) zs' zs1') (y # ys)"
      proof -
        have H: "zs1' = [zs1'e1, zs1'e2] # zs1'l" using zs1'_def by simp
        have goal: "list_split' ((zs1'e1 # zs1'e2 # tl z) # map2 (\<lambda>x y. y ! 0 # y ! Suc 0 # tl x) zss' zs1'l) (y # ys)"
        proof (rule list_split'.intros)
          show "list_split' (map2 (\<lambda>x y. y ! 0 # y ! Suc 0 # tl x) zss' zs1'l) ys"
            unfolding One_nat_def[symmetric]
          proof (rule ind[of "map tl zs"])
            show "\<And>m. m < length ys \<longrightarrow> map tl zs ! 0 ! m = zss' ! m ! 0"
            proof -
              fix m show "m < length ys \<longrightarrow> map tl zs ! 0 ! m = zss' ! m ! 0"
                using trans[of "Suc m"] zs_def zs'_def len_zs nth_tl[of m zse] by simp
            qed
          next
            show "list_split' zss' ys"
              using zss'_ys by simp
          next
            show "list_split' zs1'l (hd (map tl zs))"
              using zs1'_zs zs1'_def zs_def
              by (auto elim: list_split'.cases)
          next
            show "list_all (\<lambda>l. length l = length [x, x']) zs1'l"
              using len zs1'_def by simp
          next
            show "list_all (\<lambda>l. length l = length ys) (map tl zs)"
              using len_zs by (induction zs; simp)
          next
            show "length zs1'l = length ys"
              using len' zs1'_def by simp
          next
            show "ys \<noteq> [] \<Longrightarrow> map tl zs \<noteq> []"
              unfolding zs_def by simp
          qed
        next
          show "y = fold' (zs1'e1 # zs1'e2 # tl z)"
            using y_fold z_app zs1'_def by simp
        next
          show "zs1'e1 # zs1'e2 # tl z \<noteq> []" by simp
        qed
        show ?thesis
          using goal H
          unfolding zs'_def ze_def trans'
          by simp
      qed
    qed
    have Heq: "length zs' = length zs1'"
      using ind1 ind2
      by (cases zs) (auto dest!: list_split'_length)
    have "length zs' = length zs1' \<Longrightarrow> map2 (\<lambda>x y. y ! 0 # y ! Suc 0 # tl x) zs' zs1' ! m ! 0 = zs1' ! m ! 0" for m
    proof (induction m arbitrary: zs' zs1')
      case 0
      then show ?case by(cases zs'; cases zs1'; auto)
    next
      case (Suc m)
      then show ?case by(cases zs'; cases zs1'; auto)
    qed
    then have H3_1: "map2 (\<lambda>x y. y ! 0 # y ! Suc 0 # tl x) zs' zs1' ! m ! 0 = zs1' ! m ! 0" for m
      using Heq
      by blast
    have "length zs' = length zs1' \<Longrightarrow> map2 (\<lambda>x y. y ! 0 # y ! Suc 0 # tl x) zs' zs1' ! m ! Suc 0 = zs1' ! m ! Suc 0" for m
    proof (induction m arbitrary: zs' zs1')
      case 0
      then show ?case by(cases zs'; cases zs1'; auto)
    next
      case (Suc m)
      then show ?case by(cases zs'; cases zs1'; auto)
    qed
    then have H3_2: "\<And> m. map2 (\<lambda>x y. y ! 0 # y ! Suc 0 # tl x) zs' zs1' ! m ! Suc 0 = zs1' ! m ! Suc 0"
      using Heq
      by blast
    have H3_3: "n \<ge> 2 \<Longrightarrow> m < length zs' \<Longrightarrow> length zs' = length zs1' \<Longrightarrow> n \<le> length (zs' ! m) \<Longrightarrow> map2 (\<lambda>x y. y ! 0 # y ! Suc 0 # tl x) zs' zs1' ! m ! n = zs' ! m ! (n - 1)" for n m
    proof (induction m arbitrary: zs' zs1')
      case 0
      then show ?case
        by (cases zs'; cases zs1') (auto simp: nth_tl Suc_diff_Suc)
    next
      case (Suc m)
      then show ?case 
        by (cases zs';  cases zs1'; auto)
    qed
    have H3_help: "n < length xs \<Longrightarrow> m < length zs \<Longrightarrow> list_all (\<lambda>l. length l = Suc (length xs)) zs \<Longrightarrow> Suc (Suc n) \<le> length (zs ! m)"
      for n m and xs :: "'a list" and zs :: "'b list list" 
    proof (induction zs arbitrary: n m xs)
      case (Cons a zs)
      then show ?case 
        by(cases m; simp)
    qed simp
    have H3: "\<forall>n m. n < length xs \<longrightarrow> m < length ys \<longrightarrow> (zs1 ! 0 # zs1 ! 1 # tl zs) ! n ! m = map2 (\<lambda>zs' y. y ! 0 # y ! 1 # tl zs') zs' zs1' ! m ! n"
    proof (intro allI impI)
      fix n m
      assume hn: "n < length xs" and hm: "m < length ys"
      show "(zs1 ! 0 # zs1 ! 1 # tl zs) ! n ! m = map2 (\<lambda>zs' y. y ! 0 # y ! 1 # tl zs') zs' zs1' ! m ! n"
      proof (cases n)
        case 0
        have "zs1 ! 0 ! m = zs1' ! m ! 0"
          using ind2 len_zs1' hm by(auto dest: list_split'_length)
        then show ?thesis using \<open>n = 0\<close> by (simp add: H3_1[symmetric])
      next
        case (Suc n')
        show ?thesis
        proof (cases n')
          case 0
          have "zs1 ! 1 ! m = zs1' ! m ! 1"
            using ind2 len_zs1' hm by(auto dest: list_split'_length)
          then show ?thesis using \<open>n = Suc n'\<close> \<open>n' = 0\<close> by (simp add: H3_2[symmetric])
        next
          case (Suc n'')
          have hn2: "Suc (Suc n'') \<ge> 2" by simp
          have hm2: "m < length zs'" using ind1 hm by (auto dest: list_split'_length)
          have hlen: "length zs' = length zs1'" using Heq by simp
          have hlen2: "Suc (Suc n'') \<le> length (zs' ! m)"
            using ind1 xs_def \<open>n = Suc n'\<close> \<open>n' = Suc n''\<close> hn hm2
            by(fastforce intro: H3_help dest!: list_split'_length)
          have step1: "map2 (\<lambda>zs' y. y ! 0 # y ! 1 # tl zs') zs' zs1' ! m ! n = zs' ! m ! (n - 1)"
            using H3_3[OF hn2 hm2 hlen hlen2] \<open>n = Suc n'\<close> \<open>n' = Suc n''\<close> by simp
          have ntl: "tl zs ! n'' = zs ! Suc n''"
            using ind1 xs_def \<open>n = Suc n'\<close> \<open>n' = Suc n''\<close> hn
            by(fastforce intro: nth_tl dest: list_split'_length)
          have step2: "(zs1 ! 0 # zs1 ! 1 # tl zs) ! n ! m = zs' ! m ! (n - 1)"
            using ind1 hm ntl xs_def \<open>n = Suc n'\<close> \<open>n' = Suc n''\<close> hn
            by(fastforce dest: list_split'_length)
          with step1 show ?thesis by simp
        qed
      qed
    qed
    have H4: "list_all (\<lambda>l. length l = length ys) (zs1 ! 0 # zs1 ! 1 # tl zs)"
      using ind1 ind2
      unfolding xs_def
    proof (cases zs1)
      case Nil
      then show ?thesis using ind2 by (auto elim: list_split'.cases)
    next
      case (Cons e zss1)
      then show ?thesis using ind1 ind2 by (cases zss1) (auto intro!: list_split'.intros elim: list_split'.cases)
    qed
    have "list_all (\<lambda>l. length l = length ((x + x') # xs')) zs'" "length zs' = length zs1'"
      using ind1 Heq by auto
    then have H5: "list_all (\<lambda>l. length l = length xs) (map2 (\<lambda>zs' y. y ! 0 # y ! Suc 0 # tl zs') zs' zs1')"
      unfolding xs_def
    proof (induction zs' arbitrary: zs1')
      case Nil then show ?case by simp
    next
      case (Cons z zs') then show ?case by (cases zs1'; simp add: xs_def)
    qed
    show "\<exists>zs zs'. list_split' zs xs \<and> list_split' zs' ys \<and>
                    (\<forall>n m. n < length xs \<longrightarrow> m < length ys \<longrightarrow> zs ! n ! m = zs' ! m ! n) \<and>
                    list_all (\<lambda>l. length l = length ys) zs \<and> list_all (\<lambda>l. length l = length xs) zs'"
      using H1 H2 H3 H4 H5
      by (intro exI[where x = "zs1 ! 0 # zs1 ! 1 # tl zs"]
          exI[where x = "map2 (\<lambda>l l'. (l' ! 0) # (l' ! 1) # (tl l)) zs' zs1'"]) simp
  qed
  have list_all_len_1: "\<And>ys. list_all (\<lambda>l. length l = Suc 0) (map (\<lambda>y. [y]) ys)"
    by (simp add: list_all_length)
  consider "length xs \<le> 1" | "length ys \<le> 1" | "length xs = 2 \<and> length ys = 2" | "length xs > 2" | "length ys > 2"
    by linarith
  then show "\<exists>zs zs'. list_split' zs xs \<and> list_split' zs' ys \<and> (\<forall>n m. n < length xs \<longrightarrow> m < length ys \<longrightarrow> zs ! n ! m = zs' ! m ! n) \<and> 
        list_all (\<lambda>l. length l = length ys) zs \<and> list_all (\<lambda>l. length l = length xs) zs'"
  proof (cases, goal_cases "leq1" "leq1'" "eq2" "gt3" "gt3'")
    case leq1
    then show ?case
    proof (cases xs)
      case Nil
      then show ?thesis
        using eq_nil eq_app
        by (intro exI[where x = "[]"] exI[where x = "[]"]) (cases ys; auto intro: list_split'.intros)
    next
      case (Cons x xs')
      then show ?thesis
        using eq_nil eq_app list_all_len_1 leq1
        by (intro exI[where x = "[ys]"] exI[where x = "map (\<lambda>y. [y]) ys"])
          (auto intro: list_split'.intros list_split'_refl simp add: list_all_length)
    qed
  next
    case leq1'
    then show ?case
    proof (cases ys)
      case Nil
      then show ?thesis
        using eq_nil eq_app
        by (intro exI[where x = "[]"]) (cases xs; auto intro: list_split'.intros)
    next
      case (Cons y ys')
      then show ?thesis
        using eq_nil eq_app list_all_len_1 leq1'
        by (intro exI[where x = "map (\<lambda>x. [x]) xs"] exI[where x = "[xs]"])
          (auto intro: list_split'.intros list_split'_refl simp add: list_all_length)
    qed
  next
    case eq2
    then show ?case
    proof (cases xs; cases ys)
      fix x xs' y ys'
      assume xs_def2: "xs = x # xs'" and ys_def2: "ys = y # ys'"
      with eq2 have "length xs' = 1" "length ys' = 1" by auto
      then obtain x' y' where xs'_def: "xs' = [x']" and ys'_def: "ys' = [y']"
        by (cases xs'; cases ys'; auto)
      have heq: "x + x' = y + y'"
        using eq_app unfolding xs_def2 ys_def2 xs'_def ys'_def by simp
      obtain e11 e12 e21 e22 where
        ref: "Some x = e11 + e12" "Some x' = e21 + e22"
        "Some y = e11 + e21" "Some y' = e12 + e22"
        using refinable[OF heq] by blast
      let ?zs = "[case (e11, e12) of (Some e11', Some e12') \<Rightarrow> [e11', e12'] | (Some e11', None) \<Rightarrow> [e11', None] | (None, Some e12') \<Rightarrow> [None, e12'],
                   case (e21, e22) of (Some e21', Some e22') \<Rightarrow> [e21', e22'] | (Some e21', None) \<Rightarrow> [e21', None] | (None, Some e22') \<Rightarrow> [None, e22']]"
      let ?zs' = "[case (e11, e21) of (Some e11', Some e21') \<Rightarrow> [e11', e21'] | (Some e11', None) \<Rightarrow> [e11', None] | (None, Some e21') \<Rightarrow> [None, e21'],
                    case (e12, e22) of (Some e12', Some e22') \<Rightarrow> [e12', e22'] | (Some e12', None) \<Rightarrow> [e12', None] | (None, Some e22') \<Rightarrow> [None, e22']]"
      have zs_split: "list_split' ?zs xs"
        using ref unfolding xs_def2 xs'_def
        by (cases e11; cases e12; cases e21; cases e22)
          (auto intro!: list_split'.intros simp add: ab_semigroup_add_class.add.commute)
      have zs'_split: "list_split' ?zs' ys"
        using ref unfolding ys_def2 ys'_def
        by (cases e11; cases e12; cases e21; cases e22)
          (auto intro!: list_split'.intros simp add: ab_semigroup_add_class.add.commute)
      have cross: "\<forall>n m. n < length xs \<longrightarrow> m < length ys \<longrightarrow> ?zs ! n ! m = ?zs' ! m ! n"
        using ref unfolding xs_def2 xs'_def ys_def2 ys'_def
        by (cases e11; cases e12; cases e21; cases e22)
          (auto intro!: list_split'.intros simp add: ab_semigroup_add_class.add.commute
            | metis less_Suc0 less_antisym nth_Cons_0 nth_Cons_Suc)+
      have len_zs: "list_all (\<lambda>l. length l = length ys) ?zs"
        using ref unfolding ys_def2 ys'_def
        by (cases e11; cases e12; cases e21; cases e22) simp_all
      have len_zs': "list_all (\<lambda>l. length l = length xs) ?zs'"
        using ref unfolding xs_def2 xs'_def
        by (cases e11; cases e12; cases e21; cases e22) simp_all
      show ?thesis
        by (intro exI[where x = ?zs] exI[where x = ?zs'])
          (use zs_split zs'_split cross len_zs len_zs' in simp)
    qed (auto simp: eq2)
  next
    case gt3
    assume len: "2 < length xs"
    show ?case
      using gt3_cases len ind eq_app eq_nil
      by presburger
  next
    case gt3'
    assume len: "2 < length ys"
    have "(ys = []) = (xs = [])"
      using eq_nil by simp
    moreover have "ys \<noteq> [] \<and> xs \<noteq> [] \<longrightarrow> fold' ys = fold' xs"
      using eq_app by simp
    moreover have "length x + length ls' < length ys + length xs \<Longrightarrow>
        x \<noteq> [] \<and> ls' \<noteq> [] \<longrightarrow> fold' x = fold' ls' \<Longrightarrow>
        (x = []) = (ls' = []) \<Longrightarrow>
        \<exists>zs zs'.
           list_split' zs x \<and>
           list_split' zs' ls' \<and>
           (\<forall>n m. n < length x \<longrightarrow> m < length ls' \<longrightarrow> zs ! n ! m = zs' ! m ! n) \<and>
           list_all (\<lambda>l. length l = length ls') zs \<and> list_all (\<lambda>l. length l = length x) zs'" for x :: "'w option list" and ls'
      using ind[of x ls']
      by auto
    ultimately show ?case
      using len gt3_cases[of ys xs]
      by(simp, metis)
  qed
qed


lemma create_split_count:
  "length (zs a) = length (filter (\<lambda>(x, _). a = x) xs) \<Longrightarrow>
     count (mset (concat (zs a))) (Some w) = count (mset (create_split xs zs)) (a, w)"
  for zs :: "'a \<Rightarrow> ('w :: ref_ab_semigroup_add) option list list"
  and a :: "'a" and xs :: "('a \<times> 'w) list" and w :: "'w"
proof (induction xs arbitrary: zs)
    case Nil
    then show ?case by simp
  next
    case (Cons x xs)
    obtain x1 x2 where x_def: "x = (x1, x2)"
      by fastforce
    show ?case
    proof (cases "a = x1")
      case True
      obtain z zsa where zs_def: "zs x1 = z # zsa"
        using Cons.prems True
        unfolding x_def
        by(cases "zs a"; simp)
      have step1: "count (mset z) (Some w) = count (image_mset (Pair x1) (mset (option_list z))) (x1, w)"
      proof (induction z)
        case (Cons z1 z2) then show ?case by (cases z1; simp)
      qed simp
      have step2: "count (mset (concat zsa)) (Some w) = count (mset (create_split xs (zs(x1 := zsa)))) (x1, w)"
        using Cons.IH[of "zs(x1 := zsa)"] Cons.prems
        unfolding True x_def zs_def
        by (simp add: fun_upd_def)
      show ?thesis
        using step1 step2 zs_def
        unfolding x_def True
        by simp
    next
      case neq: False
      have cnt0: "\<And>m. count (image_mset (Pair x1) m) (a, w) = 0"
        using neq prod.inject by fastforce
      have len: "length (zs a) = length (filter (\<lambda>(x, _). a = x) xs)"
        using Cons.prems neq
        unfolding x_def
        by simp
      show ?thesis
        using Cons.IH[of "(zs(x1 := tl (zs x1)))"] neq cnt0 len
        unfolding x_def
        by (simp add: fun_upd_def)
    qed
  qed

lemma list_split_exist: 
  assumes wset_eq: "eq_wset xs ys"
  shows "\<exists>zs zs'. list_split zs xs \<and> list_split zs' ys \<and> mset zs = mset zs'"
proof -
  have foldl_eq: "Some x + foldl (+) (Some b) (map (\<lambda>x. Some (snd x)) zs) = foldl (+) (Some x + Some b) (map (\<lambda>x. Some (snd x)) zs)" for x b and zs :: "('a \<times> 'w :: ab_semigroup_add) list"
    by (induction zs arbitrary: x b) (auto simp add: plus_option_def add.left_commute add.assoc)
  have filter_eq: "filter (\<lambda>(x, _). a = x) xs = [] = (weight (abs_wset xs) a = None)" for xs  :: "('a \<times> 'w :: ref_ab_semigroup_add) list" and a
  proof (induction xs)
    case (Cons x xs)
    then show ?case
      by (cases x) (auto simp add: weight.abs_eq plus_option_def fold_Some)
  qed (simp add: wempty_def weight.abs_eq)
  have weight_wset_eq: "filter (\<lambda>(x, _). a = x) xs \<noteq> [] \<Longrightarrow> weight (abs_wset xs) a = fold' (map (\<lambda>x. Some (snd x)) (filter (\<lambda>(x, _). a = x) xs))"
    for xs :: "('a \<times> 'w :: ref_ab_semigroup_add) list" and a
  proof -
      assume hne: "filter (\<lambda>(x, _). a = x) xs \<noteq> []"
      obtain b list where hfl: "filter (\<lambda>(x, _). a = x) xs = b # list"
        using hne by (cases "filter (\<lambda>(x, _). a = x) xs") auto
      have step: "weight (abs_wset xs) a = fold' (map (\<lambda>x. Some (snd x)) (filter (\<lambda>(x, _). a = x) xs))"
      proof -
        obtain b1 b2 where b_def: "b = (b1, b2)" by fastforce
        have rhs_eq: "fold' (map (\<lambda>x. Some (snd x)) (filter (\<lambda>(x, _). a = x) xs)) =
                      foldl (+) (Some b2) (map (\<lambda>x. Some (snd x)) list)"
          unfolding hfl b_def by simp
        have lhs_eq: "weight (abs_wset xs) a =
                      fold (\<lambda>(_, w) y. Some w + y) (filter (\<lambda>(x, _). a = x) xs) None"
          by (simp add: weight.abs_eq)
        have conn: "fold (\<lambda>(_, w) y. Some w + y) ((b1, b2) # list) None =
                    foldl (+) (Some b2) (map (\<lambda>x. Some (snd x)) list)"
          by (induction list arbitrary: b2) (auto simp: add.commute add.left_commute)
        show ?thesis
          unfolding lhs_eq hfl b_def rhs_eq
          using conn by simp
      qed
      then show ?thesis by assumption
    qed
  have ind_help: "\<forall>n<length zs. \<forall>m<length zs'. zs ! n ! m = zs' ! m ! n \<Longrightarrow>
    list_all (\<lambda>l. length l = length zs') zs \<Longrightarrow> list_all (\<lambda>l. length l = length zs) zs' \<Longrightarrow> mset (concat zs) = mset (concat zs')"
    for zs :: "(('w option) list) list" and zs' :: "(('w option) list) list"
    proof (induction zs arbitrary: zs')
      case Nil
      then show ?case
        by(induction zs'; simp)
    next
      fix z :: "('w option) list"
        and zs :: "('w option) list list"
        and zs' :: "('w option) list list"
      assume ind: "\<And>zs'. \<forall>n<length zs. \<forall>m<length zs'. (zs ! n ! m::('w option)) = zs' ! m ! n \<Longrightarrow> list_all (\<lambda>l. length l = length zs') zs \<Longrightarrow> list_all (\<lambda>l. length l = length zs) zs' \<Longrightarrow> mset (concat zs) = mset (concat zs')"
        and trans: "\<forall>n<length (z # zs). \<forall>m<length zs'. (z # zs) ! n ! m = (zs' ! m ! n::('w option))"
        and len1: "list_all (\<lambda>l. length (l::('w option) list) = length (zs'::('w option) list list)) (z # zs)"
        and len2: "list_all (\<lambda>l. length (l::('w option) list) = length ((z::('w option) list) # zs)) zs'"
      have trans': "\<And>n m. n<length (z # zs) \<Longrightarrow>  m<length zs' \<Longrightarrow> (z # zs) ! n ! m = (zs' ! m ! n::('w option))"
        using trans by force
      have G1: "mset (concat zs') = mset (map hd zs') + mset (concat (map tl zs'))"
        using len2
        unfolding mset_append[symmetric]
      proof (induction zs')
        case (Cons z zs') then show ?case by (cases z; simp)
      qed simp
      have "length z = length zs'" using len1 by auto
      then have G2: "mset z = image_mset hd (mset zs')"
        using trans'[of 0] len2
      proof -
        have hd_eq: "\<forall>l \<in> set zs'. hd l = l ! 0"
        proof
          fix l assume "l \<in> set zs'"
          then have "length l = Suc (length zs)" using len2 by (simp add: list_all_iff)
          then have "l \<noteq> []" by auto
          then show "hd l = l ! 0" by (simp add: hd_conv_nth)
        qed
        have z_eq: "z = map hd zs'"
          using \<open>length z = length zs'\<close> trans'[of 0] hd_eq len2
          by (auto intro!: nth_equalityI simp: list_all_iff)
        then show ?thesis
          by simp
      qed
      have G3: "mset (concat zs) = mset (concat (map tl zs'))"
      proof (intro ind)
        show "\<forall>n<length zs. \<forall>m<length (map tl zs'). zs ! n ! m = map tl zs' ! m ! n"
        proof safe
          fix n m
          assume "n < length zs" "m < length (map tl zs')"
          then show "zs ! n ! m = map tl zs' ! m ! n"
            using trans'[of "Suc n" m] len2 by (auto simp add: nth_tl list_all_length)
        qed
      next
        show "list_all (\<lambda>l. length l = length (map tl zs')) zs"
          using len1 by simp
      next
        show "list_all (\<lambda>l. length l = length zs) (map tl zs')"
          using len2 by (induction zs' arbitrary: zs; simp)
      qed
      show "mset (concat ((z::('w option) list) # zs)) = mset (concat zs')"
        using G1 G2 G3
        by simp
    qed
  have fold_eq: "fold (\<lambda>(a, w). (+) (Some w)) lx (Some b) = fold (\<lambda>x s. s + x) (map (Some \<circ> snd) lx) (Some b)" for lx :: "('a \<times> 'w :: ref_ab_semigroup_add) list" and b :: "'w :: ref_ab_semigroup_add"
  proof (induction lx arbitrary: b)
    case Nil
    then show ?case by simp
  next
    case (Cons a lx')
    then show ?case
      by (cases a) (auto simp add: add.commute)
  qed
  have Hprev: "\<forall> a. \<exists>zs zs'.
     list_split' zs (map (Some \<circ> snd) (filter (\<lambda>(x, _). a = x) xs)) \<and>
     list_split' zs' (map (Some \<circ> snd) (filter (\<lambda>(x, _). a = x) ys)) \<and>
     (\<forall>n m. n < length (map (Some \<circ> snd) (filter (\<lambda>(x, _). a = x) xs)) \<longrightarrow> m < length (map (Some \<circ> snd) (filter (\<lambda>(x, _). a = x) ys)) \<longrightarrow> zs ! n ! m = zs' ! m ! n) \<and>
     list_all (\<lambda>l. length l = length (map (Some \<circ> snd) (filter (\<lambda>(x, _). a = x) ys))) zs \<and>
     list_all (\<lambda>l. length l = length (map (Some \<circ> snd) (filter (\<lambda>(x, _). a = x) xs))) zs'"
  proof
    fix a
    show "\<exists>zs zs'. list_split' zs (map (Some \<circ> snd) (filter (\<lambda>(x, _). a = x) xs)) \<and>
       list_split' zs' (map (Some \<circ> snd) (filter (\<lambda>(x, _). a = x) ys)) \<and>
       (\<forall>n m. n < length (map (Some \<circ> snd) (filter (\<lambda>(x, _). a = x) xs)) \<longrightarrow> m < length (map (Some \<circ> snd) (filter (\<lambda>(x, _). a = x) ys)) \<longrightarrow> zs ! n ! m = zs' ! m ! n) \<and>
       list_all (\<lambda>l. length l = length (map (Some \<circ> snd) (filter (\<lambda>(x, _). a = x) ys))) zs \<and>
       list_all (\<lambda>l. length l = length (map (Some \<circ> snd) (filter (\<lambda>(x, _). a = x) xs))) zs'"
      using wset_eq
    proof -
      show "\<exists>zs zs'. list_split' zs (map (Some \<circ> snd) (filter (\<lambda>(x, _). a = x) xs)) \<and>
         list_split' zs' (map (Some \<circ> snd) (filter (\<lambda>(x, _). a = x) ys)) \<and>
         (\<forall>n m. n < length (map (Some \<circ> snd) (filter (\<lambda>(x, _). a = x) xs)) \<longrightarrow> m < length (map (Some \<circ> snd) (filter (\<lambda>(x, _). a = x) ys)) \<longrightarrow> zs ! n ! m = zs' ! m ! n) \<and>
         list_all (\<lambda>l. length l = length (map (Some \<circ> snd) (filter (\<lambda>(x, _). a = x) ys))) zs \<and>
         list_all (\<lambda>l. length l = length (map (Some \<circ> snd) (filter (\<lambda>(x, _). a = x) xs))) zs'"
      proof (intro list_split'_exist[where xs = "(map (Some \<circ> snd) (filter (\<lambda>(x, _). a = x) xs))" and ys = "(map (Some \<circ> snd) (filter (\<lambda>(x, _). a = x) ys))"])
        show "(map (Some \<circ> snd) (filter (\<lambda>(x, _). a = x) xs) \<noteq> [] \<and> map (Some \<circ> snd) (filter (\<lambda>(x, _). a = x) ys) \<noteq> []) \<longrightarrow>
              fold' (map (Some \<circ> snd) (filter (\<lambda>(x, _). a = x) xs)) = fold' (map (Some \<circ> snd) (filter (\<lambda>(x, _). a = x) ys))"
        proof
          assume H: "map (Some \<circ> snd) (filter (\<lambda>(x, _). a = x) xs) \<noteq> [] \<and>
                     map (Some \<circ> snd) (filter (\<lambda>(x, _). a = x) ys) \<noteq> []"
          from wset_eq have eq': "sum_key xs a = sum_key ys a"
            unfolding eq_wset_def by auto
          from H obtain fx fxs fy fys
            where fx_def: "filter (\<lambda>(x, _). a = x) xs = fx # fxs"
              and fy_def: "filter (\<lambda>(x, _). a = x) ys = fy # fys"
            by (auto simp: neq_Nil_conv)
          obtain ax wx where fx_prod: "fx = (ax, wx)" by (cases fx)
          obtain ay wy where fy_prod: "fy = (ay, wy)" by (cases fy)
          show "fold' (map (Some \<circ> snd) (filter (\<lambda>(x, _). a = x) xs)) =
                fold' (map (Some \<circ> snd) (filter (\<lambda>(x, _). a = x) ys))"
            using eq' unfolding fx_def fy_def fx_prod fy_prod
            by (simp add: foldl_conv_fold fold_eq)
        qed
      next
        show "(map (Some \<circ> snd) (filter (\<lambda>(x, _). a = x) xs) = []) =
              (map (Some \<circ> snd) (filter (\<lambda>(x, _). a = x) ys) = [])"
        proof -
          have key: "sum_key xs a = sum_key ys a"
            using wset_eq unfolding eq_wset_def by simp
          have none_iff: "(map (Some \<circ> snd) (filter (\<lambda>(x, _). a = x) zs) = []) = (sum_key zs a = None)"
            for zs :: "('a \<times> 'w :: ref_ab_semigroup_add) list"          proof (induction zs)
            case Nil
            then show ?case by simp
          next
            case (Cons h t)
            obtain k v where h_def: "h = (k, v)"
              by fastforce
            then show ?case
              using Cons fold_Some
              by (cases "a = k") auto
          qed
          show ?thesis
            using none_iff[of xs] none_iff[of ys] key by simp
        qed
      qed
    qed
  qed
  then have "\<forall> a. \<exists>zs zs'. list_split' zs (map (Some \<circ> snd) (filter (\<lambda>(x,_). a = x) xs)) \<and> list_split' zs' (map (Some \<circ> snd) (filter (\<lambda>(x,_). a = x) ys)) \<and> mset (concat zs) = mset (concat zs')"
  proof -
    show "\<forall> a. \<exists>zs zs'. list_split' zs (map (Some \<circ> snd) (filter (\<lambda>(x,_). a = x) xs)) \<and> list_split' zs' (map (Some \<circ> snd) (filter (\<lambda>(x,_). a = x) ys)) \<and> mset (concat zs) = mset (concat zs')"
    proof (rule allI)
      fix a
      obtain zs_a zs'_a where
        S1: "list_split' zs_a (map (Some \<circ> snd) (filter (\<lambda>(x,_). a = x) xs))"
        and S2: "list_split' zs'_a (map (Some \<circ> snd) (filter (\<lambda>(x,_). a = x) ys))"
        and Strans: "\<forall>n m. n < length (map (Some \<circ> snd) (filter (\<lambda>(x,_). a = x) xs)) \<longrightarrow>
                           m < length (map (Some \<circ> snd) (filter (\<lambda>(x,_). a = x) ys)) \<longrightarrow>
                           zs_a ! n ! m = zs'_a ! m ! n"
        and Slen1: "list_all (\<lambda>l. length l = length (map (Some \<circ> snd) (filter (\<lambda>(x,_). a = x) ys))) zs_a"
        and Slen2: "list_all (\<lambda>l. length l = length (map (Some \<circ> snd) (filter (\<lambda>(x,_). a = x) xs))) zs'_a"
        using Hprev by blast
      have Llen1: "length zs_a = length (map (Some \<circ> snd) (filter (\<lambda>(x,_). a = x) xs))"
        by (rule list_split'_length[OF S1])
      have Llen2: "length zs'_a = length (map (Some \<circ> snd) (filter (\<lambda>(x,_). a = x) ys))"
        by (rule list_split'_length[OF S2])
      have S3: "mset (concat zs_a) = mset (concat zs'_a)"
        using Strans Slen1 Slen2 Llen1 Llen2 ind_help by metis
      show "\<exists>zs zs'. list_split' zs (map (Some \<circ> snd) (filter (\<lambda>(x,_). a = x) xs)) \<and>
                     list_split' zs' (map (Some \<circ> snd) (filter (\<lambda>(x,_). a = x) ys)) \<and>
                     mset (concat zs) = mset (concat zs')"
        using S1 S2 S3 by blast
    qed
  qed
  then obtain zs zs' where L1: "\<And> a. list_split' (zs a) (map (Some \<circ> snd) (filter (\<lambda>(x,_). a = x) xs))" and 
    L2: "\<And> a. list_split' (zs' a) (map (Some \<circ> snd) (filter (\<lambda>(x,_). a = x) ys))" and L3: "\<And> a. mset (concat (zs a)) = mset (concat (zs' a))"
    by metis
  have G: "(\<forall> a. list_split' (zs a) (map (Some \<circ> snd) (filter (\<lambda>(x,_). a = x) xs))) \<Longrightarrow> list_split (create_split xs zs) xs"
    for zs :: "'a \<Rightarrow> ('w :: ref_ab_semigroup_add) option list list" and xs
    proof (induction xs arbitrary: zs)

      fix zs :: "'a \<Rightarrow> 'w option list list"
      assume "\<forall>a. list_split' (zs (a::'a)) (map (Some \<circ> snd) (filter (\<lambda>(x, y). ((\<lambda>_. a = x)::'w \<Rightarrow> bool) y) []))"
      show "list_split (create_split [] zs) []"
        by(auto intro: list_split.intros)
    next
      fix x :: "'a \<times> 'w"
        and xs :: "('a \<times> 'w) list"
        and zs :: "'a \<Rightarrow> 'w option list list"
      assume ind1: "\<And>zs. (\<forall>a. list_split' (zs a) (map (Some \<circ> snd) (filter (\<lambda>(x, _). a = x) xs))) \<Longrightarrow> list_split (create_split xs zs) xs"
        and ind2: "\<forall>a. list_split' (zs a) (map (Some \<circ> snd) (filter (\<lambda>(x, _). a = x) (x # xs)))"
      have ind1: "\<And>zs. (\<And>a. list_split' (zs a) (map (Some \<circ> snd) (filter (\<lambda>(x, _). a = x) xs))) \<Longrightarrow> list_split (create_split xs zs) xs"
        and ind2: "\<And>a. list_split' (zs a) (map (Some \<circ> snd) (filter (\<lambda>(x, _). a = x) (x # xs)))"
        using ind1 ind2 by auto
      obtain x1 x2 where x_def: "x = (x1,x2)"
        by fastforce
      have H1: "list_split (create_split xs (zs(x1 := tl (zs x1)))) xs"
      proof (rule ind1)
        fix a
        show "list_split' ((zs(x1 := tl (zs x1))) a) (map (Some \<circ> snd) (filter (\<lambda>(x, _). a = x) xs))"
          using ind2[of a] unfolding x_def by (auto elim: list_split'.cases)
      qed
      have H2: "create_split ((x1, x2) # xs) zs = map (Pair x1) (option_list (hd (zs x1))) @ create_split xs (zs(x1 := tl (zs x1)))"
        by simp
      have H3: "x2 = fold' (map snd (map (Pair x1) (option_list (hd (zs x1)))))"
      proof (cases "zs x1")
        case Nil
        then show ?thesis
          using ind2[of x1] unfolding x_def using list_split'.cases by fastforce
      next
        case (Cons h t)
        then show ?thesis
          using ind2[of x1] unfolding x_def comp_def
        proof -
          assume hcons: "zs x1 = h # t"
            and ls: "list_split' (zs x1) (map (\<lambda>x. Some (snd x)) (filter (\<lambda>(x, _). x1 = x) ((x1, x2) # xs)))"
          have filt: "map (\<lambda>x. Some (snd x)) (filter (\<lambda>(x, _). x1 = x) ((x1, x2) # xs)) = Some x2 # map (\<lambda>x. Some (snd x)) (filter (\<lambda>(x, _). x1 = x) xs)"
            by simp
          have "list_split' (h # t) (Some x2 # map (\<lambda>x. Some (snd x)) (filter (\<lambda>(x, _). x1 = x) xs))"
            using ls hcons filt by simp
          then have fold_h: "Some x2 = fold' h" and h_ne: "h \<noteq> []"
            by (auto elim: list_split'.cases)
          have "x2 = fold' (option_list h)"
            by (rule fold_option[OF fold_h h_ne])
          then show "x2 = fold' (map snd (map (Pair x1) (option_list (hd (zs x1)))))"
            by (simp add: hcons comp_def)
        qed
      qed
      have H4: "map (Pair x1) (option_list (hd (zs x1))) \<noteq> []"
      proof (cases "zs x1")
        case Nil
        then show ?thesis
          using ind2[of x1] unfolding x_def using list_split'.cases by fastforce
      next
        case (Cons h t)
        then show ?thesis
          using ind2[of x1] unfolding x_def
          by (auto elim: list_split'.cases simp add: fold_option_not_none)
      qed
      have "list_all (\<lambda>(a, b). a = x1) (map (Pair x1) (option_list l))" for l :: "'c option list"
        proof (induction l)
          case (Cons a l) then show ?case by (cases a) auto
        qed simp
      then have H5: "list_all (\<lambda>(a, b). a = x1) (map (Pair x1) (option_list (hd (zs x1))))"
        by auto
      show "list_split (create_split (x # xs) zs) (x # xs)"
        using H1 H2 H3 H4 H5 Split
        unfolding x_def by fast
    qed
  have G3: "mset (create_split xs zs) = mset (create_split ys zs')"
  proof (rule multiset_eqI)
    fix x
    show "count (mset (create_split xs zs)) x = count (mset (create_split ys zs')) x"
      using L1[THEN list_split'_length] L2[THEN list_split'_length]
      by (cases x) (auto simp: L3 simp flip: create_split_count)
  qed
  show ?thesis
    using G L1 L2 G3
    by blast
qed

lemma w_size_eq_Suc_imp_eq_union:
  assumes H: "size M = Suc n"
  shows "\<exists>x w N. M = wupdate N x (Some w) \<and> weight N x = None"
proof -
  have H1: "\<exists>x w. weight M x = Some w"
  proof -
    obtain l where M_eq: "M = abs_wset l" using get_abs_wset by blast
    obtain m1 m2 l' where l_eq: "l = (m1, m2) # l'"
    proof (cases l)
      case Nil
      then have "wset M = {}" by (simp add: M_eq wset.abs_eq)
      then have "size M = 0" by (simp add: size_wset_overloaded_def)
      with H show ?thesis by simp
    next
      case (Cons m l')
      obtain m1 m2 where "m = (m1, m2)" by (cases m)
      then show ?thesis using that Cons by blast
    qed
    have not_none: "fold (\<lambda>(a, w). (+) (Some w)) (filter (\<lambda>(e', _). m1 = e') l') (Some m2) \<noteq> None"
      by (rule fold_Some)
    obtain v where "fold (\<lambda>(a, w). (+) (Some w)) (filter (\<lambda>(e', _). m1 = e') l') (Some m2) = Some v"
      using not_none by (cases "fold (\<lambda>(a, w). (+) (Some w)) (filter (\<lambda>(e', _). m1 = e') l') (Some m2)") auto
    then show ?thesis
      by (auto simp add: M_eq l_eq weight.abs_eq)
  qed
  then obtain x w where Hxw: "weight M x = Some w" by blast
  show ?thesis
  proof (intro exI conjI)
    show "M = wupdate (wupdate M x None) x (Some w)"
      by (simp add: weight_eq_iff[symmetric] Hxw)
    show "weight (wupdate M x None) x = None"
      by simp
  qed
qed

lemma size_wupdate: 
  assumes size: "Suc k = size (wupdate N x (Some w))"
    and weight: "weight N x = None"
  shows "k = size N"
proof -
  obtain l where N_def: "N = abs_wset l"
    by (metis get_abs_wset)
  have "list_all (\<lambda>(a, _). x \<noteq> a) l"
    using weight
    unfolding N_def weight.abs_eq
  proof (induction l)
    case Nil then show ?case by simp
  next
    case (Cons h t) then show ?case
      by (metis (mono_tags, lifting) filter.simps(2) fold_Some(1) fold_simps(2)
          list.pred_inject(2) plus_option_simps(1) split_beta)
  qed
  then have set_eq: "{y. (\<exists>b. (y, b) \<in> set l) \<and> x \<noteq> y} - {x} = {y. \<exists>x\<in>set l. y = fst x}"
    by(auto simp add: Bex_def Ball_set_list_all[symmetric])
  have fin: "finite {y. (\<exists>b. (y, b) \<in> set l) \<and> x \<noteq> y}"
  proof -
    have "finite (Domain (set l))"
      using finite_Domain by blast
    then show ?thesis
      by (simp add: Domain_unfold)
  qed
  show ?thesis
    using size set_eq fin
    unfolding N_def size_wset_overloaded_def
    by(auto simp add: wset.abs_eq wupdate.abs_eq weight.abs_eq image_def card.insert_remove)
qed

theorem wset_induct [case_names empty add, induct type: multiset]:
  assumes empty: "\<And> M. M = wempty \<Longrightarrow> P M"
    and add: "\<And>x w M. P M \<Longrightarrow> weight M x = None \<Longrightarrow> P (wupdate M x (Some w))"
  shows "P M"
proof (induct "size M" arbitrary: M)
  fix M :: "('a, 'b) wset"
  assume size: "0 = size M"
  obtain l where M_def: "M = abs_wset l"
    using get_abs_wset
    by auto
  show "P M"
  proof (rule empty)
    show "M = wempty"
      using size
      unfolding weight_eq_iff[symmetric]
      by (auto simp add: M_def size_wset_overloaded_def wset.abs_eq weight.abs_eq)
  qed
next
  fix k :: nat
    and M :: "('a, 'b) wset"
  assume ind: "\<And>M. k = size M \<Longrightarrow> P M"
    and size: "Suc k = size M"
  obtain N x w where M_def: "M = wupdate N x (Some w)" and weight_N: "weight N x = None"
    using size[symmetric] w_size_eq_Suc_imp_eq_union
    by blast
  show "P M"
    using size weight_N ind[of N] size_wupdate add
    unfolding M_def
    by metis
qed

section \<open>The Negative Representation\<close>

lemma weight_inj: "inj weight" 
  unfolding inj_def by transfer (auto simp: eq_wset_def fun_eq_iff)

lemma type_definition_wset: "type_definition weight (inv weight) {f :: 'a \<Rightarrow> ('w :: ref_ab_semigroup_add) option. finite {x. f x \<noteq> None}}"
proof standard
  fix x :: "('a, 'w) wset"
  have H1 : "finite {e. list_ex (\<lambda>x. fst x = e) kxs}" for kxs :: "('a \<times> 'w :: ref_ab_semigroup_add) list"
    by(induction kxs; simp)
  have H2: "{e. \<exists>y. sum_key kxs e = Some y} \<subseteq> {e. list_ex (\<lambda>x. fst x = e) kxs}" for kxs :: "('a \<times> 'w :: ref_ab_semigroup_add) list"
    by (induction kxs) auto

  show "weight x \<in> {f. finite {x. f x \<noteq> None}}"
    using H1[of "(rep_wset x)"] H2[of "(rep_wset x)"]
    by (auto simp add: weight.rep_eq intro: rev_finite_subset)
next
  fix x :: "('a, 'w) wset"
  show "inv weight (weight x) = x"
    by (rule inv_f_f, rule weight_inj)
next
  fix f :: "'a \<Rightarrow> 'w option"
  assume fin: "f \<in> {f. finite {x. f x \<noteq> None}}"
  show "weight (inv weight f) = f"
  proof (rule f_inv_into_f)
    show "f \<in> range weight"
    proof -
      have "\<exists>x. f = weight x"
      proof (rule finite_Map_induct[of f "\<lambda>f. \<exists>x. f = weight x"])
        show "finite (dom f)"
          using fin unfolding dom_def by simp
      next
        show "\<exists>x. (\<lambda>_. None) = weight x"
          by (rule exI[where x = wempty]) simp
      next
        fix x :: 'a and w :: 'w and f' :: "'a \<Rightarrow> 'w option"
        assume "finite (dom f')" "x \<notin> dom f'" and IH: "\<exists>ws. f' = weight ws"
        then obtain ws where ws_def: "f' = weight ws" by blast
        show "\<exists>x2. f'(x \<mapsto> w) = weight x2"
        proof (rule exI[where x = "wupdate ws x (Some w)"])
          show "f'(x \<mapsto> w) = weight (wupdate ws x (Some w))"
            by (simp add: ws_def)
        qed
      qed
      then show ?thesis by (simp add: image_def)
    qed
  qed
qed

lemma weight_finite: "finite {x. \<exists>y. weight M x = Some y}"
  using type_definition_wset
  unfolding type_definition_def by auto

lemma wadd_assoc: "wadd x (wadd y z) = wadd (wadd x y) z"
  by transfer auto

lemma wadd_commute: "wadd x y = wadd y x"
  by transfer (auto simp: eq_wset_append_sym)

lemma wadd_wsingle[simp]: "wadd (wsingle x w) ws = wupdate ws x (Some w + weight ws x)"
  unfolding weight_eq_iff[symmetric] by auto

lemma w_list_all2_split_left_invariance:
  "list_all2 (rel_prod R (=)) xs ys \<Longrightarrow> list_split xs' xs \<Longrightarrow>
  \<exists>ys'. list_all2 (rel_prod R (=)) xs' ys' \<and> list_split ys' ys"
proof (induction xs arbitrary: ys xs')
  fix ys :: "('c \<times> 'b) list"
    and xs' :: "('a \<times> 'b) list"
  assume "list_all2 (rel_prod R (=)) [] ys"
    and "list_split xs' []"
  then show "\<exists>ys'. list_all2 (rel_prod R (=)) xs' ys' \<and> list_split ys' ys"
    by(cases xs'; auto elim: list_split.cases)
next
  fix x :: "'a \<times> 'b"
    and xs :: "('a \<times> 'b) list"
    and ys :: "('c \<times> 'b) list"
    and xs' :: "('a \<times> 'b) list"
  assume ind: "\<And>ys (xs' :: ('a \<times> 'b) list). list_all2 (rel_prod R (=)) xs ys \<Longrightarrow> list_split xs' xs \<Longrightarrow> \<exists>ys'. list_all2 (rel_prod R (=)) xs' ys' \<and> list_split ys' ys"
    and list2_all': "list_all2 (rel_prod R (=)) (x # xs) ys"
    and list_split': "list_split xs' (x # xs)"
  have "ys \<noteq> []"
    using list2_all'
    by auto
  then obtain x' wx y' wy yss where ys_def: "ys = (y', wy) # yss" and x_def: "x = (x', wx)"
    using list2_all'
    by (metis list.exhaust surj_pair)
  have wx_def: "wx = wy"
    using list2_all' x_def ys_def
    by fastforce
  have R_x_y: "R x' y'"
    using list2_all' x_def ys_def
    by simp
  obtain exs exs' where list_split': "list_split exs' xs" and xs'_def: "xs' = exs @ exs'" and 
    wy_fold: "wy = fold' (map snd exs)" and exs_nonempty: "exs \<noteq> []" and list_all_exs: "list_all (\<lambda>(a,b). a = x') exs"
    using list_split' x_def wx_def
    by(auto elim: list_split.cases)
  obtain eys' where ind_e: "list_all2 (rel_prod R (=)) exs' eys'" and wset_yss: "list_split eys' yss"
    using list2_all' list_split' x_def ys_def ind eq_wset_sym
    by fastforce
  have "exs \<noteq> [] \<Longrightarrow> list_split eys' yss \<Longrightarrow> list_split (map (\<lambda>(_, w). (y', w)) exs @ eys') ((y', fold' (map snd exs)) # yss)"
  proof (induction "length exs" arbitrary: exs)
    case 0
    then show ?case
      by simp
  next
    fix n :: nat
      and exs :: "('a \<times> 'b) list"
    assume ind: "\<And>exs. n = length (exs::('a \<times> 'b) list) \<Longrightarrow> exs \<noteq> [] \<Longrightarrow> list_split eys' yss \<Longrightarrow> list_split (map (\<lambda>(_, y). (y', y)) exs @ eys') ((y', fold' (map snd exs)) # yss)"
      and length: "Suc n = length (exs::('a \<times> 'b) list)"
      and non_empty: "(exs::('a \<times> 'b) list) \<noteq> []"
      and eq: "list_split eys' yss"
    obtain e11 e12 exs' where exs_def : "exs = (e11,e12) # exs'"
      by (metis list.exhaust old.prod.exhaust non_empty)
    consider "exs' = []" | "exs' \<noteq> []"
      by fast
    then show "list_split (map (\<lambda>(_, y). (y', y)) (exs::('a \<times> 'b) list) @ eys') ((y', fold' (map snd exs)) # yss)"
    proof (cases, goal_cases "nil" "not_nil'")
      case nil
      then show ?case
        unfolding exs_def
        by(auto simp add: foldl_assoc add.assoc eq_wset_sym eq intro!: eq_wset_elem_remove list_split_cons_eq)
    next
      case not_nil'
      then obtain e21 e22 exs'' where exs'_def : "exs' = (e21,e22) # exs''"
        by (metis list.exhaust old.prod.exhaust)
      have H_len: "n = length ((e11, e12+e22) # exs'')"
        using length unfolding exs_def exs'_def by simp
      have H_ih: "list_split (map (\<lambda>(_, y). (y', y)) ((e11, e12+e22) # exs'') @ eys') ((y', fold' (map snd ((e11, e12+e22) # exs''))) # yss)"
        using ind[of "(e11, e12+e22) # exs''"] H_len eq by simp
      have H_comb: "list_split ((y', e12) # (y', e22) # map (\<lambda>(_, y). (y', y)) exs'' @ eys') ((y', e12+e22) # map (\<lambda>(_, y). (y', y)) exs'' @ eys')"
        using list_split_comb[of y' e12 e22 "map (\<lambda>(_, y). (y', y)) exs'' @ eys'"] by simp
      show ?case
        unfolding exs_def exs'_def
        using list_split_trans[OF H_comb] H_ih
        by (simp add: foldl_assoc[of "(+)"] add.assoc)
    qed
  qed
  then have "list_split (map (\<lambda>(_, w). (y', w)) exs @ eys') ((y', wy) # yss)"
    using exs_nonempty wset_yss
    by(simp add:  wx_def wy_fold wset.abs_eq_iff)
  also have "list_all2 (rel_prod R (=)) xs' (map (\<lambda>(_, w). (y', w)) exs @ eys')"
    using R_x_y list_all_exs ind_e
    unfolding xs'_def
    by (induction exs) auto
  ultimately show "\<exists>ys'. list_all2 (rel_prod R (=)) xs' ys' \<and> list_split ys' ys"
    unfolding ys_def x_def
    by (intro exI[where x = "(map (\<lambda>(_,w). (y',w)) exs) @ eys'"]) auto
qed

lemma w_list_all2_split_right_invariance:
  "list_all2 (rel_prod R (=)) xs ys \<Longrightarrow> list_split ys' ys \<Longrightarrow>
  \<exists>xs'. list_all2 (rel_prod R (=)) xs' ys' \<and> list_split xs' xs"
  using w_list_all2_split_left_invariance list.rel_flip
  by (metis conversep_eq prod.rel_conversep)

lemma w_list_all2_reorder_left_invariance:
  "list_all2 (rel_prod R (=)) xs ys \<Longrightarrow> list_split xs' xs \<Longrightarrow>
  \<exists>ys'. list_all2 (rel_prod R (=)) xs' ys' \<and> eq_wset ys' ys"
  using w_list_all2_split_left_invariance list_split_eq_wset
  by metis

lemma w_list_all2_reorder_right_invariance:
  "list_all2 (rel_prod R (=)) xs ys \<Longrightarrow> list_split ys' ys \<Longrightarrow>
  \<exists>xs'. list_all2 (rel_prod R (=)) xs' ys' \<and> eq_wset xs' xs"
  using w_list_all2_reorder_left_invariance list.rel_flip
  by (metis conversep_eq prod.rel_conversep)

lemma eq_wset_remove1: "ListMem x xs \<Longrightarrow> eq_wset (x # (remove1 x xs)) xs"
proof(induction "length xs" arbitrary: x xs)
  case 0
  then show ?case 
    by(auto elim: ListMem.cases)
next
  case (Suc n)
  then show ?case
  proof (cases xs)
    case Nil
    with Suc show ?thesis by auto
  next
    case (Cons x' xs')
    then show ?thesis
    proof (cases "x = x'")
      case True
      then show ?thesis
        unfolding eq_wset_def
        using Cons by simp
    next
      case False
      then show ?thesis
        using Cons Suc.hyps(1) eq_wset_elem_switch eq_wset_elem_remove
        using ListMem_iff[of x xs] Suc.prems eq_wset_elem_back[of _ x]
          eq_wset_elem_back'[of x "remove1 x xs"] eq_wset_sym[of xs "remove1 x xs @ [x]"]
          eq_wset_trans[of "x # remove1 x xs" "remove1 x xs @ [x]" xs]
          remove1_split[of x xs "remove1 x xs"] by fastforce
    qed
  qed
qed

lemma wset_mset_list:
  "mset (xs :: ('a \<times> 'w :: ref_ab_semigroup_add) list) = mset ys \<Longrightarrow>
  abs_wset xs = abs_wset ys"
proof (induction "xs" arbitrary: ys)
  fix ys :: "('a \<times> 'w) list"
  assume "mset [] = mset ys"
  then show "abs_wset [] = abs_wset ys"
    by force
next
  fix x :: "'a \<times> 'w"
    and xs :: "('a \<times> 'w) list"
    and ys :: "('a \<times> 'w) list"
  obtain x' w where x_def: "x = (x', w)"
    by force
  assume ind: "\<And>ys. mset xs = mset ys \<Longrightarrow> abs_wset xs = abs_wset ys"
    and mset_eq: "mset (x # xs) = mset ys"
  have H: "ListMem (x', w) ys"
    using mset_eq
    by (metis ListMem_iff list.set_intros(1) set_mset_mset x_def)
  then have wset_ys: "abs_wset ys = wadd (wsingle x' w) (abs_wset (remove1 (x', w) ys))"
    by(simp add: wsingle.abs_eq wadd.abs_eq wset.abs_eq_iff eq_wset_remove1 eq_wset_sym)
  have wset_xs: "eq_wset xs (remove1 (x', w) ys)"
    using ind mset_eq
    by (metis mset_remove1 remove1.simps(2) x_def wset.abs_eq_iff[symmetric])
  show "abs_wset (x # xs) = abs_wset ys"
    by(auto simp add: wset_ys wset_xs x_def wsingle.abs_eq wadd.abs_eq wset.abs_eq_iff intro!: eq_wset_elem_remove)
qed

lemma fold_some': "fold (\<lambda>(a, w). (+) (Some w)) (x # xs) w \<noteq> None"
  by (induction xs arbitrary: x w) (auto simp: plus_option_case)

lemma eq_wset_mset:
  "mset (xs :: ('a \<times> 'w :: ref_ab_semigroup_add) list) = mset ys \<Longrightarrow> eq_wset xs ys"
proof (induction "xs" arbitrary: ys)
  fix ys :: "('a \<times> 'w) list"
  assume "mset [] = mset ys"
  then show "eq_wset [] ys"
    unfolding eq_wset_def
    by force
next
  fix x :: "'a \<times> 'w"
    and xs :: "('a \<times> 'w) list"
    and ys :: "('a \<times> 'w) list"
  obtain x' w where x_def: "x = (x', w)"
    by force
  assume ind: "\<And>ys. mset xs = mset ys \<Longrightarrow> eq_wset xs ys"
    and mset_eq: "mset (x # xs) = mset ys"
  have "ListMem (x', w) ys"
    using mset_eq
    by (metis ListMem_iff list.set_intros(1) set_mset_mset x_def)
  then have wset_ys: "eq_wset ys ((x', w) # (remove1 (x', w) ys))"
    using eq_wset_remove1 eq_wset_sym
    by blast
  have wset_xs: "eq_wset xs (remove1 (x', w) ys)"
    using ind mset_eq
    by (metis mset_remove1 remove1.simps(2) x_def)
  show "eq_wset (x # xs) ys"
    unfolding x_def
    using wset_ys wset_xs eq_wset_sym eq_wset_elem_remove
    using eq_wset_trans by blast
qed

lemma eq_wset_set_fst:
  assumes A: "eq_wset xs ys"
  shows "fst ` set xs = fst ` set ys"
proof -
  have H1: "(\<exists> x \<in> set xs. a = fst x) = (fold (\<lambda>(_, w). (+) (Some w)) (filter (\<lambda>(a',_). a = a') xs) None \<noteq> None)" for a :: 'a and xs :: "('a \<times> 'w :: ref_ab_semigroup_add) list"
  proof (cases "filter (\<lambda>(a', _). a = a') xs")
    case Nil
    then have no_match: "\<forall>x\<in>set xs. a \<noteq> fst x"
      by (simp add: filter_empty_conv split_beta)
    then have "sum_key xs a = None"
      by (simp add: Nil)
    then show ?thesis using no_match by simp
  next
    case (Cons x xs')
    then show ?thesis
    proof (cases x)
      case (Pair a' w)
      then show ?thesis
        using Cons by (auto simp: fold_Some' filter_eq_Cons_iff)
    qed
  qed
  show ?thesis
    using A
    unfolding image_def eq_wset_def
    by(auto simp: eq_wset_def image_def H1 fold_Some')
qed

section \<open>BNF Registration\<close>

lift_bnf ('a, dead 'w :: ref_ab_semigroup_add) wset
  for map: wimage rel: wrel
proof -
  fix Ps :: "'a \<Rightarrow> 'b \<Rightarrow> bool" and Qs :: "'b \<Rightarrow> 'c \<Rightarrow> bool"
  assume "Ps OO Qs \<noteq> bot"
  show "list_all2 (rel_prod Ps (=)) OO eq_wset OO list_all2 (rel_prod Qs (=)) \<le>
        (eq_wset :: ('a \<times> 'w) list \<Rightarrow> _) OO list_all2 (rel_prod (Ps OO Qs) (=)) OO (eq_wset :: ('c \<times> 'w) list \<Rightarrow> _)"
  proof safe
    fix xs :: "('a \<times> 'w :: ref_ab_semigroup_add) list" and zs :: "('c \<times> 'w) list"
      and ys :: "('b \<times> 'w) list" and y's :: "('b \<times> 'w) list"
    assume lall_Ps: "list_all2 (rel_prod Ps (=)) xs ys"
      and eq_ys: "eq_wset ys y's"
      and lall_Qs: "list_all2 (rel_prod Qs (=)) y's zs"
    obtain ys' y's' where
      split_ys: "list_split ys' ys" and split_y's: "list_split y's' y's"
      and mset_eq: "mset ys' = mset y's'"
      using list_split_exist[OF eq_ys] by blast
    obtain xs' where xs'_lall: "list_all2 (rel_prod Ps (=)) xs' ys'"
      and xs'_eq: "eq_wset xs' xs"
      using w_list_all2_reorder_right_invariance[OF lall_Ps split_ys] by blast
    obtain zs' where zs'_lall: "list_all2 (rel_prod Qs (=)) y's' zs'"
      and zs'_eq: "eq_wset zs' zs"
      using w_list_all2_reorder_left_invariance[OF lall_Qs split_y's] by blast
    obtain ys'' where ys''_lall: "list_all2 (rel_prod Qs (=)) ys' ys''"
      and ys''_mset: "mset ys'' = mset zs'"
      using list_all2_reorder_left_invariance[OF zs'_lall mset_eq] by blast
    show "(eq_wset OO list_all2 (rel_prod (Ps OO Qs) (=)) OO eq_wset) xs zs"
    proof (intro relcomppI)
      show "eq_wset xs xs'"
        using xs'_eq eq_wset_sym by blast
      show "eq_wset ys'' zs"
        using eq_wset_mset eq_wset_trans ys''_mset zs'_eq by blast
      show "list_all2 (rel_prod (Ps OO Qs) (=)) xs' ys''"
        by (smt (verit, best) list_all2_trans rel_prod_sel relcomppI xs'_lall ys''_lall)
    qed
  qed
next
  have H: "\<Union> (Basic_BNFs.fsts ` set xs) = (set o (map fst)) xs" for xs :: "('a \<times> 'w :: ref_ab_semigroup_add) list"
    by (induction xs) auto
  show "(Ss :: 'a set set) \<noteq> {} \<Longrightarrow> \<Inter> Ss \<noteq> {} \<Longrightarrow>
          (\<Inter>As\<in>Ss. {(x, x'). eq_wset x x'} `` {x :: ('a \<times> 'w) list. \<Union> (Basic_BNFs.fsts ` set x) \<subseteq> As}) \<subseteq> {(x, x'). eq_wset x x'} `` {x. \<Union> (Basic_BNFs.fsts ` set x) \<subseteq> \<Inter> Ss}" for Ss
    unfolding H
    using Inter_greatest[of Ss "(set o map fst) _"]
    unfolding subset_eq Ball_def Bex_def INT_iff Image_iff mem_Collect_eq prod.case
    by (metis comp_apply eq_wset_fst eq_wset_refl)
qed

section \<open>Further Operations\<close>

lift_definition wfilter :: \<open>('a \<Rightarrow> bool) \<Rightarrow> ('a, 'w :: ref_ab_semigroup_add) wset \<Rightarrow> ('a, 'w :: ref_ab_semigroup_add) wset\<close> is
  \<open>\<lambda>f l. filter (\<lambda>x. f (fst x)) l\<close>
  unfolding eq_wset_def
proof (safe)
  fix f :: "'a \<Rightarrow> bool" and l1 l2 :: "('a \<times> 'w) list" and q :: 'a
  assume H: "\<forall>q. sum_key l1 q = sum_key l2 q"
  show "sum_key (filter (\<lambda>x. f (fst x)) l1) q = sum_key (filter (\<lambda>x. f (fst x)) l2) q"
  proof (cases "f q")
    case True
    then show ?thesis
      using H[rule_format, of q]
      unfolding filter_filter
      by (metis (mono_tags, lifting) case_prod_beta filter_cong)
  next
    case False
    then show ?thesis
      unfolding filter_filter
      by (metis (mono_tags, lifting) case_prod_beta filter_False)
  qed
qed

definition wimage_option :: \<open>('a \<Rightarrow> 'b option) \<Rightarrow> ('a, 'w :: ref_ab_semigroup_add) wset \<Rightarrow> ('b, 'w :: ref_ab_semigroup_add) wset\<close> where
  "wimage_option f ws = wimage ((case_option (SOME x. True) id) o f) (wfilter ((case_option False (\<lambda>_. True)) o f) ws)"

lemma rep_wset_wempty[simp]: "rep_wset wempty = ([] :: ('a \<times> ('b :: ref_ab_semigroup_add)) list)"
  unfolding wempty_def
  using Quotient_rep_abs[OF Quotient_wset, of "[] :: ('a \<times> 'b) list"]
  by (cases "rep_wset (abs_wset ([] :: ('a \<times> 'b) list))") auto

lemma wadd_wsingle_wempty[simp]: "wadd (wsingle x w) wempty = wsingle x w"
  by transfer simp

lemma wempty_if_None: "(\<And>x. weight w x = None) \<Longrightarrow> w = wempty"
  by transfer (simp add: eq_wset_def)

section \<open>Switching Between Representations\<close>

locale wset_as_pfun begin
setup_lifting type_definition_wset

lemma wempty_transfer[transfer_rule]: "pcr_wset R1 R2 (\<lambda>x. None) wempty"
  unfolding wempty_def pcr_wset_def cr_wset_def option.rel_eq fun.rel_eq eq_OO weight.abs_eq
  unfolding rel_fun_def
  by(rule relcomppI[of _ _ "weight (abs_wset [])"]; (simp add: weight.abs_eq)?)

lemma weight_transfer[transfer_rule]: "rel_fun (pcr_wset (=) (=)) (rel_fun (=) (=)) (\<lambda>ws x. ws x) weight"
  unfolding wsingle_def pcr_wset_def cr_wset_def option.rel_eq fun.rel_eq eq_OO map_fun_def comp_def
  unfolding rel_fun_def
  by simp

lemma in_set_conv_sum_key_Some: "x \<in> fst ` set kvs \<longleftrightarrow> (\<exists>v. sum_key kvs x = Some v)"
proof (induction kvs)
  case Nil
  show ?case by simp
next
  case (Cons kv kvs)
  obtain k v where kv_def: "kv = (k, v)" by (cases kv)
  show ?case
  proof (cases "k = x")
    case True
    then show ?thesis
      by (auto simp: kv_def fold_Some')
  next
    case False
    then show ?thesis
      using Cons.IH by (auto simp: kv_def)
  qed
qed

lemma wset_transfer[transfer_rule]: "rel_fun (pcr_wset (=) (=)) (=) (\<lambda>ws. {x. ws x \<noteq> None}) wset"
  by (auto simp: rel_fun_def pcr_wset_def cr_wset_def option.rel_eq wset.rep_eq weight.rep_eq
      in_set_conv_sum_key_Some del: imageE)

lemma wsingle_transfer[transfer_rule]: "rel_fun (=) (rel_fun (=) (pcr_wset (=) (=))) (\<lambda>x w x'. if x = x' then Some w else None) wsingle"
  by (auto simp: rel_fun_def pcr_wset_def cr_wset_def option.rel_eq relcompp_apply)

lemma wadd_transfer[transfer_rule]: "rel_fun (pcr_wset (=) (=)) (rel_fun (pcr_wset (=) (=)) (pcr_wset (=) (=))) (\<lambda>ws ws' x. ws x + ws' x) wadd"
  by (auto simp: rel_fun_def pcr_wset_def cr_wset_def option.rel_eq relcompp_apply)

lemma wupdate_transfer[transfer_rule]: "rel_fun (pcr_wset (=) (=)) (rel_fun (=) (rel_fun (=) (pcr_wset (=) (=)))) (\<lambda>ws x w x'. if x = x' then w else ws x') wupdate"
  by (auto simp: rel_fun_def pcr_wset_def cr_wset_def option.rel_eq relcompp_apply)

lemma fold_eq_wset: "eq_wset l l' \<Longrightarrow> sum_key (map (map_prod f id) l') x = sum_key (map (map_prod f id) l) x"
proof -
  assume A: "eq_wset l l'"
  have H2: "sum_key (map (map_prod f id) l) x = 
            sum_key (map (map_prod f id) (filter g l)) x +
            sum_key (map (map_prod f id) (filter (\<lambda>x. \<not> g x) l)) x " for f :: "'a \<Rightarrow> 'c" and g :: "'a \<times> 'b \<Rightarrow> bool" and l :: "('a \<times> 'b :: ref_ab_semigroup_add) list" and x :: 'c
  proof (induction l)
    show "sum_key (map (map_prod f id) []) x = sum_key (map (map_prod f id) (filter g [])) x + sum_key (map (map_prod f id) (filter (\<lambda>x. \<not> g x) [])) x"
      by simp
  next
    fix a :: "'a \<times> 'b"
      and l :: "('a \<times> 'b :: ref_ab_semigroup_add) list"
    assume ind: "fold (\<lambda>a. case a of (a, w) \<Rightarrow> (+) (Some w)) (filter (\<lambda>a. case a of (a', uu_) \<Rightarrow> x = a') (map (map_prod f id) l)) None = fold (\<lambda>a. case a of (a, w) \<Rightarrow> (+) (Some w)) (filter (\<lambda>a. case a of (a', uu_) \<Rightarrow> x = a') (map (map_prod f id) (filter g l))) None + fold (\<lambda>a. case a of (a, w) \<Rightarrow> (+) (Some w)) (filter (\<lambda>a. case a of (a', uu_) \<Rightarrow> x = a') (map (map_prod f id) (filter (\<lambda>x. \<not> g x) l))) None"
    then show "fold (\<lambda>a. case a of (a, w) \<Rightarrow> (+) (Some w)) (filter (\<lambda>a. case a of (a', uu_) \<Rightarrow> x = a') (map (map_prod f id) (a # l))) None = fold (\<lambda>a. case a of (a, w) \<Rightarrow> (+) (Some w)) (filter (\<lambda>a. case a of (a', uu_) \<Rightarrow> x = a') (map (map_prod f id) (filter g (a # l)))) None + fold (\<lambda>a. case a of (a, w) \<Rightarrow> (+) (Some w)) (filter (\<lambda>a. case a of (a', uu_) \<Rightarrow> x = a') (map (map_prod f id) (filter (\<lambda>x. \<not> g x) (a # l)))) None"
      by(auto simp add: fold_Some_out add.commute[symmetric] add.assoc[symmetric])
  qed
  have H3': "(\<lambda>p. (case p of (a', uu_) \<Rightarrow> a = a') \<and> (case map_prod f id p of (a', uu_) \<Rightarrow> x = a')) = (\<lambda>(a', _). a = a' \<and> f a = x)" for x :: 'c and f :: "'a \<Rightarrow> 'c" and a :: 'a
    by force
  have H3'': "(\<lambda>x. case map_prod f id x of (a, w) \<Rightarrow> (+) (Some w)) = (\<lambda>(a, w) \<Rightarrow> (+) (Some w))" for f :: "'a \<Rightarrow> 'c"
    by fastforce
  have H3: "fold (\<lambda>(a, w). (+) (Some w)) (filter (\<lambda>(a', _). x = a') (map (map_prod f id) (filter (\<lambda>(a', _). a = a') l))) None = 
            fold (\<lambda>(a, w). (+) (Some w)) (filter (\<lambda>(a', _). a = a' \<and> f a = x) l) None" for x :: 'c and f :: "'a \<Rightarrow> 'c" and a :: 'a and l :: "('a \<times> 'b :: ref_ab_semigroup_add) list"
    unfolding filter_map comp_def filter_filter fold_map H3' H3''
    by simp
  have "eq_wset l l' \<Longrightarrow> sum_key (map (map_prod f id) l') x = sum_key (map (map_prod f id) l) x"
  proof (induction "map fst l" arbitrary: l l' rule: length_induct)
    fix l :: "('a \<times> 'b) list"
      and l' :: "('a \<times> 'b) list"
    assume ind: "\<forall>ys. length ys < length (map fst l) \<longrightarrow> (\<forall>(la :: ('a \<times> 'b) list). ys = map fst la \<longrightarrow> (\<forall>lb. eq_wset la lb \<longrightarrow> 
                sum_key (map (map_prod f id) lb) x = sum_key (map (map_prod f id) la) x))"
      and l_l'_eq: "eq_wset (l::('a \<times> 'b) list) l'"
    have ind: "\<And>(l' :: ('a \<times> 'b) list) l''. length (map fst l') < length (map fst l)  \<Longrightarrow> eq_wset l' l'' \<Longrightarrow>
                sum_key (map (map_prod f id) l'') x = sum_key (map (map_prod f id) l') x"
      using ind
      by metis
    consider "l = []" | "l \<noteq> []"
      by auto
    then show "fold (\<lambda>(a, w). (+) (Some (w::'b))) (filter (\<lambda>(a', _). x = a') (map (map_prod f id) l')) None = fold (\<lambda>(a, w). (+) (Some w)) (filter (\<lambda>(a', _). x = a') (map (map_prod f id) l)) None"
    proof (cases, goal_cases "nil" "app")
      case nil
      have l'_def: "l' = []"
        using l_l'_eq fold_Some(2)
        unfolding nil eq_wset_def
        by (metis (mono_tags, lifting) filter.simps(1) fold_Some_back fold_elem_back' fold_simps(1) list.collapse prod.exhaust_sel)
      show ?case
        unfolding nil l'_def
        by simp
    next
      case app
      obtain a1 a2 l1 where l_def: "l = (a1, a2) # l1"
        using app
        by (metis neq_Nil_conv old.prod.exhaust)
      have A1': "a \<noteq> a1 \<Longrightarrow> (\<lambda>x. \<not> (case x of (a', uu_) \<Rightarrow> a1 = a') \<and> (case x of (a', uu_) \<Rightarrow> a = a')) = (\<lambda>(a', _). a = a')" for a
        by (rule ext) force
      have A1: "eq_wset (filter (\<lambda>x. \<not> (case x of (a', uu_) \<Rightarrow> a1 = a')) l) (filter (\<lambda>x. \<not> (case x of (a', uu_) \<Rightarrow> a1 = a')) l')"
        using l_l'_eq
        unfolding eq_wset_def filter_filter
      proof (safe)
        fix a
        assume H: "\<forall>q. sum_key l q = sum_key l' q"
        show "fold (\<lambda>(_, w). (+) (Some w)) (filter (\<lambda>x. \<not> (case x of (a', _) \<Rightarrow> a1 = a') \<and> (case x of (a', _) \<Rightarrow> a = a')) l) None =
              fold (\<lambda>(_, w). (+) (Some w)) (filter (\<lambda>x. \<not> (case x of (a', _) \<Rightarrow> a1 = a') \<and> (case x of (a', _) \<Rightarrow> a = a')) l') None"
          using H[rule_format, of a]
          by (cases "a = a1"; simp add: A1'[of a])
      qed
      have A2: "length (map fst (filter (\<lambda>x. \<not> (case x of (a', uu_) \<Rightarrow> a1 = a')) l)) < length (map fst l)"
        unfolding l_def length_map list.size add_Suc_right add_0_right less_Suc_eq_le
        by simp
      show ?case 
        using l_l'_eq A1[THEN ind[of "filter (\<lambda>x. \<not> (case x of (a', uu_) \<Rightarrow> a1 = a')) l" "filter (\<lambda>x. \<not> (case x of (a', uu_) \<Rightarrow> a1 = a')) l'", OF A2]]
        unfolding H2[of x f l "\<lambda>(a', _). a1 = a'"] H2[of x f l' "\<lambda>(a', _). a1 = a'"] eq_wset_def H3
        by (cases "f a1 = x") simp_all
    qed
  qed
  then show ?thesis
    using A
    by blast
qed

lemma wimage_transfer[transfer_rule]: "rel_fun (=) (rel_fun (pcr_wset (=) (=)) (pcr_wset (=) (=)))
     (\<lambda>f M b. Finite_Set.fold (\<lambda>x. (+) (M x)) None {a. M a \<noteq> None \<and> f a = b}) wimage"
proof -
  have H: "Finite_Set.fold (\<lambda>x. (+) (weight ws x)) None {a. (\<exists>y. weight ws a = Some y) \<and> f a = x} = weight (abs_wset (map (map_prod f id) (rep_wset ws))) x" for f :: "'a \<Rightarrow> 'b" and ws :: "('a, 'w :: ref_ab_semigroup_add) wset" and x :: 'b
  proof (induction ws rule: wset.abs_induct)
    fix l :: "('a \<times> 'w :: ref_ab_semigroup_add) list"
    have "Finite_Set.fold (\<lambda>x. (+) (sum_key l x)) w
           {a. (\<exists>v. sum_key l a = Some v) \<and> f a = x} =
           fold (\<lambda>(a, w). (+) (Some w)) (filter (\<lambda>(a', _). x = a') (map (map_prod f id) l)) w" for w
    proof (induction l arbitrary: w)
      fix w :: "'w :: ref_ab_semigroup_add option"
      show "Finite_Set.fold (\<lambda>x. (+) (sum_key [] x)) w {b. (\<exists>v. sum_key [] b = Some v) \<and> f b = x} =
      fold (\<lambda>(a, w). (+) (Some w)) (filter (\<lambda>(a', _). x = a') (map (map_prod f id) [])) w"
        by simp
    next
      fix a :: "'a \<times> 'w"
        and l :: "('a \<times> 'w :: ref_ab_semigroup_add) list"
        and w :: "'w :: ref_ab_semigroup_add option"
      obtain a1 a2 where a_def: "a = (a1, a2)"
        by fastforce
      assume ind: "\<And>w. Finite_Set.fold (\<lambda>x. (+) (sum_key l x)) w {a. (\<exists>v. sum_key l a = Some v) \<and> f a = x} =
             fold (\<lambda>(a, w). (+) (Some w)) (filter (\<lambda>(a', _). x = a') (map (map_prod f id) l)) w"
      consider "f a1 = x" | "f a1 \<noteq> x"
        by fast
      then show "Finite_Set.fold (\<lambda>x. (+) (sum_key (a # l) x)) w {b. (\<exists>v. sum_key (a # l) b = Some v) \<and> f b = x} = fold (\<lambda>(a, w). (+) (Some w)) (filter (\<lambda>(a', _). x = a') (map (map_prod f id) (a # l))) w"
      proof (cases, goal_cases "eq" "neq")
        case eq
        have A1': "{b. (\<exists>v. sum_key l b = Some v) \<and> f b = x} \<subseteq> set (map fst l)" for l :: "('a \<times> 'w :: ref_ab_semigroup_add) list"
          by (induction l) auto
        have cfco_al: "comp_fun_commute_on UNIV (\<lambda>x. (+) (sum_key (a # l) x))"
          unfolding comp_fun_commute_on_def comp_def
          by (simp add: add.left_commute)
        have fin_al: "finite {b. (\<exists>v. sum_key (a # l) b = Some v) \<and> f b = x}"
          by (rule rev_finite_subset[of "set (map fst (a # l))"])
            (simp, unfold a_def, use eq A1' in blast)
        have mem_al: "a1 \<in> {b. (\<exists>v. sum_key (a # l) b = Some v) \<and> f b = x}"
          by(cases "sum_key l a1"; simp add: a_def eq fold_Some_out)
        have A1: "Finite_Set.fold (\<lambda>x. (+) (sum_key (a # l) x)) w
                   {b. (\<exists>v. sum_key (a # l) b = Some v) \<and> f b = x} =
                  (sum_key (a # l) a1) + 
                  Finite_Set.fold (\<lambda>x. (+) (sum_key (a # l) x)) w
                   ({b. (\<exists>v. sum_key (a # l) b = Some v) \<and> f b = x} - {a1})"
          by (rule comp_fun_commute_on.fold_rec[OF cfco_al subset_UNIV fin_al mem_al])
        have A2: "Finite_Set.fold (\<lambda>x. (+) (sum_key (a # l) x)) w ({b. (\<exists>v. sum_key (a # l) b = Some v) \<and> f b = x} - {a1}) =
                    Finite_Set.fold (\<lambda>x. (+) (sum_key l x)) w ({b. (\<exists>v. sum_key (a # l) b = Some v) \<and> f b = x} - {a1})"
          by(rule fold_closed_eq[of _ UNIV]; simp add: eq a_def)
        consider "sum_key l a1 = None" | "sum_key l a1 \<noteq> None"
          by linarith
        then show ?case 
        proof (cases, goal_cases "None" "Some")
          case None
          have A3: "{b. (\<exists>v. sum_key (a # l) b = Some v) \<and> f b = x} - {a1} = {b. (\<exists>v. sum_key l b = Some v) \<and> f b = x}"
            by(auto simp add: None a_def eq fold_Some_out)
          show ?case
            unfolding A1 A2
            unfolding A3 ind
            by(cases w; simp add: fold_Some_out a_def eq None add.commute add.assoc[symmetric])
        next
          case Some
          have A3: "{b. (\<exists>v. sum_key (a # l) b = Some v) \<and> f b = x} - {a1} = {b. (\<exists>v. sum_key l b = Some v) \<and> f b = x} - {a1}"
            by(auto simp add: Some a_def eq fold_Some_out)
          have cfco_l: "comp_fun_commute_on UNIV (\<lambda>x. (+) (sum_key l x))"
            unfolding comp_fun_commute_on_def comp_def
            by (simp add: add.left_commute)
          have fin_l: "finite {b. (\<exists>v. sum_key l b = Some v) \<and> f b = x}"
            by (metis (lifting) A3 finite_insert finite.emptyI fin_al finite_Diff2)
          have mem_l: "a1 \<in> {b. (\<exists>v. sum_key l b = Some v) \<and> f b = x}"
            using Some eq by blast
          have A4: "sum_key l a1 + Finite_Set.fold (\<lambda>x. (+) (sum_key l x)) w ({b. (\<exists>v. sum_key l b = Some v) \<and> f b = x} - {a1}) =
                      Finite_Set.fold (\<lambda>x. (+) (sum_key l x)) w {b. (\<exists>v. sum_key l b = Some v) \<and> f b = x}"
            by (rule comp_fun_commute_on.fold_rec[symmetric, OF cfco_l subset_UNIV fin_l mem_l])
          have A5: "fold (\<lambda>(a, w). (+) (Some w)) (filter (\<lambda>(a', _). a1 = a') (a # l)) None +
                    Finite_Set.fold (\<lambda>x. (+) (fold (\<lambda>(a, w). (+) (Some w)) (filter (\<lambda>(a', _). x = a') l) None)) w
                     ({b. (\<exists>v. fold (\<lambda>(a, w). (+) (Some w)) (filter (\<lambda>(a', _). b = a') l) None = Some v) \<and> f b = x} - {a1}) = 
                    Some a2 + (fold (\<lambda>(a, w). (+) (Some w)) (filter (\<lambda>(a', _). a1 = a') l) None +
                    Finite_Set.fold (\<lambda>x. (+) (fold (\<lambda>(a, w). (+) (Some w)) (filter (\<lambda>(a', _). x = a') l) None)) w
                     ({b. (\<exists>v. fold (\<lambda>(a, w). (+) (Some w)) (filter (\<lambda>(a', _). b = a') l) None = Some v) \<and> f b = x} - {a1}))"
            by(simp add: add.commute add.assoc[symmetric] fold_Some_out a_def)
          show ?case
            unfolding A1 A2
            unfolding A3 A4 A5 ind
            by(cases w; simp add: add.commute add.assoc[symmetric] fold_Some_out a_def eq)
        qed
      next
        case neq
        have set_eq: "{b. (\<exists>v. sum_key (a # l) b = Some v) \<and> f b = x} = {b. (\<exists>v. sum_key l b = Some v) \<and> f b = x}"
          using neq a_def
          by force
        from neq have Fold_eq: "Finite_Set.fold (\<lambda>x. (+) (sum_key (a # l) x)) w {a. (\<exists>v. sum_key l a = Some v) \<and> f a = x} =
                         Finite_Set.fold (\<lambda>x. (+) (sum_key l x)) w {a. (\<exists>v. sum_key l a = Some v) \<and> f a = x}"
          by (intro fold_closed_eq[of _ UNIV]) (auto simp: a_def)
        show ?case
          unfolding set_eq Fold_eq
          using ind[of w] a_def neq
          by simp
      qed
    qed
    then show "Finite_Set.fold (\<lambda>x. (+) (weight (abs_wset l) x)) None {a. (\<exists>v. weight (abs_wset l) a = Some v) \<and> f a = x} = weight (abs_wset (map (map_prod f id) (rep_wset (abs_wset l)))) x"
      unfolding  weight.abs_eq fold_eq_wset[OF eq_wset_refl[THEN Weighted_Set.Quotient_wset[THEN Quotient_rep_abs], of l], symmetric]
      by fast
  qed
  show ?thesis
    unfolding wimage_def pcr_wset_def cr_wset_def option.rel_eq fun.rel_eq eq_OO map_fun_def comp_def
    unfolding rel_fun_def
    by(simp add: H)
qed

lemma wfilter_transfer[transfer_rule]: "rel_fun (rel_fun (=) (=)) (rel_fun (pcr_wset (=) (=)) (pcr_wset (=) (=)))
     (\<lambda>f M b. case (M b, f b) of (Some b', True) \<Rightarrow> Some b' | _ \<Rightarrow> None) wfilter"
proof -
  have "( case fold (\<lambda>(a, w). (+) (Some w)) (filter (\<lambda>(a', _). x = a') xs) v of None \<Rightarrow> None
     | Some b' \<Rightarrow> (case ws x of True \<Rightarrow> Some b' | False \<Rightarrow> None)) =
    fold (\<lambda>(a, w). (+) (Some w))
     (filter (\<lambda>aw. ws (fst aw) \<and> (case aw of (a', _) \<Rightarrow> x = a')) xs) v"
    if "v \<noteq> None \<longrightarrow> ws x"
    for x :: 'a and ws :: "'a \<Rightarrow> bool" and ws' :: "'a \<Rightarrow> bool" and v :: "'w :: ref_ab_semigroup_add option" and xs :: "('a \<times> 'w :: ref_ab_semigroup_add) list" and c :: bool
  proof (cases "ws x")
    case True
    have filter_eq: "(filter (\<lambda>aw. ws (fst aw) \<and> (case aw of (a', _) \<Rightarrow> x = a')) xs) =
                    (filter (\<lambda>(a', _). x = a') xs)"
      by (rule filter_cong) (auto simp: True case_prod_beta)
    show ?thesis by (simp add: True filter_eq split: option.splits)
  next
    case False
    then have v_None: "v = None" using that by simp
    have filter_empty: "filter (\<lambda>aw. ws (fst aw) \<and> (case aw of (a', _) \<Rightarrow> x = a')) xs = []"
      by (rule filter_False) (auto simp add: False case_prod_beta)
    have lhs_None: "(case fold (\<lambda>(a, w). (+) (Some w)) (filter (\<lambda>(a', _). x = a') xs) v of
                     None \<Rightarrow> None | Some b' \<Rightarrow> if ws x then Some b' else None) = None"
    proof (cases "filter (\<lambda>(a', _). x = a') xs")
      case Nil
      then show ?thesis by (simp add: v_None)
    next
      case (Cons h t)
      then have "fold (\<lambda>(a, w). (+) (Some w)) (filter (\<lambda>(a', _). x = a') xs) v \<noteq> None"
        unfolding v_None using fold_some' by metis
      then obtain b' where "fold (\<lambda>(a, w). (+) (Some w)) (filter (\<lambda>(a', _). x = a') xs) v = Some b'"
        by blast
      then show ?thesis by (simp add: False)
    qed
    show ?thesis by (simp add: filter_empty lhs_None v_None False split: option.splits bool.splits)
  qed
  then show ?thesis unfolding rel_fun_def pcr_wset_def cr_wset_def option.rel_eq relcompp_apply wfilter_def
      weight.abs_eq map_fun_def o_apply
    by (auto simp: weight.rep_eq)
qed

end

lemma wimage_empty[simp]: "wimage f wempty = wempty"
  by (transfer) (simp add: eq_wset_def)

lemma wimage_wadd_wsingle: "wimage f (wadd (wsingle x w) M) = wadd (wsingle (f x) w) (wimage f M)"
  by (transfer) (auto simp add: eq_wset_def)

lemma wimage_wsingle[simp]: "wimage f (wsingle x w) = (wsingle (f x) w)"
  by (transfer) (auto simp add: eq_wset_def)

lemma wimage_wadd[simp]: "wimage f (wadd xs ys) = wadd (wimage f xs) (wimage f ys)"
  by (transfer) auto

lemma w_image_update:
  "weight M x = None \<Longrightarrow> wimage f (wupdate M x (Some w)) = wadd (wsingle (f x) w) (wimage f M)"
proof(transfer, safe)
  fix M :: "('b \<times> ('a :: ref_ab_semigroup_add)) list"
    and x :: 'b
    and f :: "'b \<Rightarrow> 'c"
    and w :: 'a
  assume "sum_key M x = None"
  then have filter_M_eq: "filter (\<lambda>(x', _). x \<noteq> x') M = M"
  proof (induction M)
    case Nil
    then show ?case by simp
  next
    case (Cons h t)
    then show ?case by (auto simp add: fold_Some)
  qed
  show "eq_wset
        (map (map_prod f id)
          (case Some w of None \<Rightarrow> filter (\<lambda>(x', _). x \<noteq> x') M
           | Some w' \<Rightarrow> (x, w') # filter (\<lambda>(x', _). x \<noteq> x') M))
        ([(f x, w)] @ map (map_prod f id) M)"
    by(simp add: filter_M_eq)
qed

lifting_update wset.lifting
lifting_forget wset.lifting

locale Quotient_wset begin
setup_lifting Weighted_Set.Quotient_wset Weighted_Set.wset_equivp[THEN equivp_reflp2]
end

lemma abs_wset_rep_wset: "abs_wset (rep_wset x) = x"
  by (rule Quotient_abs_rep[OF Quotient_wset])
lemma abs_wset_cons: "abs_wset ((x,w) # xs) = wadd (wsingle x w) (abs_wset xs)"
  by transfer auto

lemma abs_wset_map: "abs_wset (map (map_prod f id) xs) = wimage f (abs_wset xs)"
  by transfer auto

context begin
interpretation wset_as_pfun.

lemma rep_wset_set:
  assumes "(a, w) \<in> set (rep_wset z)"
  shows "\<exists>y. weight z a = Some y"
proof -
  have H: "(a, w) \<in> set xs \<Longrightarrow> \<exists>y. sum_key xs a = Some y" for a :: 'a and w :: "'w :: ref_ab_semigroup_add" and xs :: "('a \<times> 'w :: ref_ab_semigroup_add) list"
  proof (induction xs)
    case Nil then show ?case by simp
  next
    case (Cons x xs)
    then show ?case by (cases x; auto simp add: fold_Some')
  qed
  then show ?thesis
    using assms
    unfolding weight_def
    by(simp add: H)
qed

lemma set_wset_in: "x \<in> set_wset ws = (weight (ws :: ('a, 'w :: ref_ab_semigroup_add) wset) x \<noteq> None)"
proof -
  have H1: "filter (\<lambda>(a', _). e = a') xs \<noteq> [] \<Longrightarrow> sum_key (map (map_prod Inr id) xs) (Inr e) \<noteq> None" for e :: 'a and xs :: "('a \<times> 'w :: ref_ab_semigroup_add) list"
  proof (induction xs)
    case Nil then show ?case by simp
  next
    case (Cons x xs)
    then show ?case by (cases x; cases "e = fst x"; auto simp add: fold_Some)
  qed
  have key: "(\<forall>zs. eq_wset (map (map_prod Inr id) (rep_wset ws)) zs \<longrightarrow>
              (\<exists>zs\<in>set zs. \<exists>zs\<in>Basic_BNFs.fsts zs. x \<in> Basic_BNFs.setr zs)) =
             (\<exists>y. weight ws x = Some y)"
  proof (rule iffI)
    assume H: "\<forall>zs. eq_wset (map (map_prod Inr id) (rep_wset ws)) zs \<longrightarrow>
              (\<exists>z\<in>set zs. \<exists>a\<in>Basic_BNFs.fsts z. x \<in> Basic_BNFs.setr a)"
    have mem: "\<exists>aw\<in>set (rep_wset ws). x = fst aw"
    proof -
      from H[THEN spec[where x = "map (map_prod Inr id) (rep_wset ws)"],
          simplified eq_wset_refl simp_thms]
      show ?thesis
        by (simp add: image_def Bex_def Basic_BNFs.fsts.simps Basic_BNFs.setr.simps)
    qed
    then obtain a w where "(a, w) \<in> set (rep_wset ws)" and "x = a" by auto
    then show "\<exists>y. weight ws x = Some y" by (blast dest: rep_wset_set)
  next
    assume H: "\<exists>y. weight ws x = Some y"
    show "\<forall>zs. eq_wset (map (map_prod Inr id) (rep_wset ws)) zs \<longrightarrow>
              (\<exists>zs\<in>set zs. \<exists>zs\<in>Basic_BNFs.fsts zs. x \<in> Basic_BNFs.setr zs)"
    proof (rule allI, rule impI)
      fix zs :: "(('d + 'a) \<times> 'w) list"
      assume Heq: "eq_wset (map (map_prod Inr id) (rep_wset ws)) zs"
      from H obtain y where Hweight: "weight ws x = Some y" by blast
      have sk_ne: "sum_key (map (map_prod Inr id) (rep_wset ws)) (Inr x) \<noteq> None"
      proof -
        from Hweight have "weight ws x \<noteq> None" by simp
        then show ?thesis
          unfolding weight_def
          by (cases "filter (\<lambda>(a', _). x = a') (rep_wset ws)") (simp_all add: H1)
      qed
      have sk_zs: "sum_key zs (Inr x) \<noteq> None"
        using Heq sk_ne unfolding eq_wset_def by metis
      show "\<exists>zs\<in>set zs. \<exists>zs\<in>Basic_BNFs.fsts zs. x \<in> Basic_BNFs.setr zs"
      proof -
        from sk_zs obtain v where "sum_key zs (Inr x) = Some v" by fastforce
        then have "Inr x \<in> fst ` set zs" by (simp add: in_set_conv_sum_key_Some)
        then obtain p where hp: "p \<in> set zs" and "fst p = Inr x" by auto
        then show ?thesis
          by (auto simp add: Basic_BNFs.fsts.simps Basic_BNFs.setr.simps intro: bexI[OF _ hp])
      qed
    qed
  qed
  then show ?thesis unfolding set_wset_def by simp
qed



lemma set_wset_alt_def: "set_wset ws = {x. weight ws x \<noteq> None}"
  using set_wset_in
  by fast

lemma wrel_alt_def:
  fixes x :: "('a, 'w :: ref_ab_semigroup_add) wset" and y :: "('b, 'w) wset"
  shows "wrel R x y = (\<exists>xs ys. abs_wset xs = x \<and> list_all2 (rel_prod R (=)) xs ys \<and> abs_wset ys = y)"
  unfolding wset.in_rel set_wset_alt_def
proof safe
  fix z :: "('a \<times> 'b, 'w) wset"
  assume "{x. weight z x \<noteq> None} \<subseteq> {(x, y). R x y}"
  then have "list_all2 (rel_prod R (=)) (map (\<lambda>((a,b),c). (a,c)) (rep_wset z)) (map (\<lambda>((a,b),c). (b,c)) (rep_wset z))"
    unfolding list.rel_map by (auto intro!: list.rel_refl_strong simp: subset_eq dest: rep_wset_set)
  moreover have "abs_wset (map (\<lambda>((a,b),c). (a,c)) (rep_wset z)) = wimage fst z"
    by (metis (no_types, lifting) abs_wset_map abs_wset_rep_wset id_apply map_eq_conv map_prod_def split_beta)
  moreover have "abs_wset (map (\<lambda>((a,b),c). (b,c)) (rep_wset z)) = wimage snd z"
    by (metis (no_types, lifting) abs_wset_map abs_wset_rep_wset id_apply map_eq_conv map_prod_def split_beta)
  ultimately show "\<exists>xs ys. abs_wset xs = wimage fst z \<and> list_all2 (rel_prod R (=)) xs ys \<and> abs_wset ys = wimage snd z"
    by blast
next
  fix xs :: "('a \<times> 'w) list" and ys :: "('b \<times> 'w) list"
  assume "list_all2 (rel_prod R (=)) xs ys"
  then obtain zs :: "(('a \<times> 'w) \<times> ('b \<times> 'w)) list" where zs: "map fst zs = xs" "map snd zs = ys"
    "set zs \<subseteq> {(x, y). rel_prod R (=) x y}"
    unfolding list.in_rel by blast
  let ?zs = "abs_wset (map (\<lambda>((a, _), (b, w)). ((a, b), w)) zs)"
  from zs(3) have "?zs \<in> {x. {a. weight x a \<noteq> None} \<subseteq> {(x, y). R x y}}"
    by (induct zs) (auto simp: weight.abs_eq)
  moreover from zs(1,3) have "wimage fst ?zs = abs_wset xs"
    by (force simp flip: abs_wset_map simp: wset.abs_eq_iff eq_wset_def
        intro!: arg_cong2[where f = sum_key])
  moreover from zs(2) have "wimage snd ?zs = abs_wset ys"
    by (force simp flip: abs_wset_map simp: wset.abs_eq_iff eq_wset_def
        intro!: arg_cong2[where f = sum_key])
  ultimately show "\<exists>z. z \<in> {M. {xy. weight M xy \<noteq> None} \<subseteq> {(x, y). R x y}} \<and>
    wimage fst z = abs_wset xs \<and> wimage snd z = abs_wset ys"
    by blast
qed

end

declare [[typedef_overloaded]]
codatatype ('a, 'w) wsetinf = WSetInf "(('a, 'w) wsetinf + 'a, 'w :: ref_ab_semigroup_add) wset"

end
