subsection \<open>A Comparator-Interface to Red-Black-Trees\<close>

theory RBT_Comparator_Impl
imports 
  "HOL-Library.RBT_Impl"
  Comparator
begin

text \<open>For all of the main algorithms of red-black trees, we
  provide alternatives which are completely based on comparators,
  and which are provable equivalent. At the time of writing,
  this interface is used in the Container AFP-entry.
  
  It does not rely on the modifications of code-equations as in 
  the previous subsection.\<close>

context 
  fixes c :: "'a comparator"
begin

primrec rbt_comp_lookup :: "('a, 'b) rbt \<Rightarrow> 'a \<rightharpoonup> 'b"
where
  "rbt_comp_lookup RBT_Impl.Empty k = None"
| "rbt_comp_lookup (Branch _ l x y r) k = 
   (case c k x of Lt \<Rightarrow> rbt_comp_lookup l k 
     | Gt \<Rightarrow> rbt_comp_lookup r k 
     | Eq \<Rightarrow> Some y)"

fun
  rbt_comp_ins :: "('a \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> ('a,'b) rbt \<Rightarrow> ('a,'b) rbt"
where
  "rbt_comp_ins f k v RBT_Impl.Empty = Branch RBT_Impl.R RBT_Impl.Empty k v  RBT_Impl.Empty" |
  "rbt_comp_ins f k v (Branch RBT_Impl.B l x y r) = (case c k x of 
      Lt \<Rightarrow> balance (rbt_comp_ins f k v l) x y r
    | Gt \<Rightarrow> balance l x y (rbt_comp_ins f k v r)
    | Eq \<Rightarrow> Branch RBT_Impl.B l x (f k y v) r)" |
  "rbt_comp_ins f k v (Branch RBT_Impl.R l x y r) = (case c k x of 
      Lt \<Rightarrow> Branch RBT_Impl.R (rbt_comp_ins f k v l) x y r
    | Gt \<Rightarrow> Branch RBT_Impl.R l x y (rbt_comp_ins f k v r)
    | Eq \<Rightarrow> Branch RBT_Impl.R l x (f k y v) r)"

definition rbt_comp_insert_with_key :: "('a \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> ('a,'b) rbt \<Rightarrow> ('a,'b) rbt"
where "rbt_comp_insert_with_key f k v t = paint RBT_Impl.B (rbt_comp_ins f k v t)"

definition rbt_comp_insert :: "'a \<Rightarrow> 'b \<Rightarrow> ('a, 'b) rbt \<Rightarrow> ('a, 'b) rbt" where
  "rbt_comp_insert = rbt_comp_insert_with_key (\<lambda>_ _ nv. nv)"

fun
  rbt_comp_del_from_left :: "'a \<Rightarrow> ('a,'b) rbt \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> ('a,'b) rbt \<Rightarrow> ('a,'b) rbt" and
  rbt_comp_del_from_right :: "'a \<Rightarrow> ('a,'b) rbt \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> ('a,'b) rbt \<Rightarrow> ('a,'b) rbt" and
  rbt_comp_del :: "'a\<Rightarrow> ('a,'b) rbt \<Rightarrow> ('a,'b) rbt"
where
  "rbt_comp_del x RBT_Impl.Empty = RBT_Impl.Empty" |
  "rbt_comp_del x (Branch _ a y s b) = 
   (case c x y of 
        Lt \<Rightarrow> rbt_comp_del_from_left x a y s b 
      | Gt \<Rightarrow> rbt_comp_del_from_right x a y s b
      | Eq \<Rightarrow> combine a b)" |
  "rbt_comp_del_from_left x (Branch RBT_Impl.B lt z v rt) y s b = balance_left (rbt_comp_del x (Branch RBT_Impl.B lt z v rt)) y s b" |
  "rbt_comp_del_from_left x a y s b = Branch RBT_Impl.R (rbt_comp_del x a) y s b" |
  "rbt_comp_del_from_right x a y s (Branch RBT_Impl.B lt z v rt) = balance_right a y s (rbt_comp_del x (Branch RBT_Impl.B lt z v rt))" | 
  "rbt_comp_del_from_right x a y s b = Branch RBT_Impl.R a y s (rbt_comp_del x b)"

definition "rbt_comp_delete k t = paint RBT_Impl.B (rbt_comp_del k t)"

definition "rbt_comp_bulkload xs = foldr (\<lambda>(k, v). rbt_comp_insert k v) xs RBT_Impl.Empty"

primrec
  rbt_comp_map_entry :: "'a \<Rightarrow> ('b \<Rightarrow> 'b) \<Rightarrow> ('a, 'b) rbt \<Rightarrow> ('a, 'b) rbt"
where
  "rbt_comp_map_entry k f RBT_Impl.Empty = RBT_Impl.Empty"
| "rbt_comp_map_entry k f (Branch cc lt x v rt) =
    (case c k x of 
        Lt \<Rightarrow> Branch cc (rbt_comp_map_entry k f lt) x v rt
      | Gt \<Rightarrow> Branch cc lt x v (rbt_comp_map_entry k f rt)
      | Eq \<Rightarrow> Branch cc lt x (f v) rt)"

function comp_sunion_with :: "('a \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> ('a \<times> 'b) list \<Rightarrow> ('a \<times> 'b) list \<Rightarrow> ('a \<times> 'b) list" 
where
  "comp_sunion_with f ((k, v) # as) ((k', v') # bs) =
   (case c k' k of 
        Lt \<Rightarrow> (k', v') # comp_sunion_with f ((k, v) # as) bs
      | Gt \<Rightarrow> (k, v) # comp_sunion_with f as ((k', v') # bs)
      | Eq \<Rightarrow> (k, f k v v') # comp_sunion_with f as bs)"
| "comp_sunion_with f [] bs = bs"
| "comp_sunion_with f as [] = as"
by pat_completeness auto
termination by lexicographic_order

function comp_sinter_with :: "('a \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> ('a \<times> 'b) list \<Rightarrow> ('a \<times> 'b) list \<Rightarrow> ('a \<times> 'b) list"
where
  "comp_sinter_with f ((k, v) # as) ((k', v') # bs) =
  (case c k' k of 
      Lt \<Rightarrow> comp_sinter_with f ((k, v) # as) bs
    | Gt \<Rightarrow> comp_sinter_with f as ((k', v') # bs)
    | Eq \<Rightarrow> (k, f k v v') # comp_sinter_with f as bs)"
| "comp_sinter_with f [] _ = []"
| "comp_sinter_with f _ [] = []"
by pat_completeness auto
termination by lexicographic_order

fun rbt_split_comp :: "('a, 'b) rbt \<Rightarrow> 'a \<Rightarrow> ('a, 'b) rbt \<times> 'b option \<times> ('a, 'b) rbt" where
  "rbt_split_comp RBT_Impl.Empty k = (RBT_Impl.Empty, None, RBT_Impl.Empty)"
| "rbt_split_comp (RBT_Impl.Branch _ l a b r) x = (case c x a of
    Lt \<Rightarrow> (case rbt_split_comp l x of (l1, \<beta>, l2) \<Rightarrow> (l1, \<beta>, rbt_join l2 a b r))
  | Gt \<Rightarrow> (case rbt_split_comp r x of (r1, \<beta>, r2) \<Rightarrow> (rbt_join l a b r1, \<beta>, r2))
  | Eq \<Rightarrow> (l, Some b, r))"

lemma rbt_split_comp_size: "(l2, b, r2) = rbt_split_comp t2 a \<Longrightarrow> size l2 + size r2 \<le> size t2"
  by (induction t2 a arbitrary: l2 b r2 rule: rbt_split_comp.induct)
     (auto split: order.splits if_splits prod.splits)

function rbt_comp_union_rec :: "('a \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> ('a, 'b) rbt \<Rightarrow> ('a, 'b) rbt \<Rightarrow> ('a, 'b) rbt" where
  "rbt_comp_union_rec f t1 t2 = (let (f, t2, t1) =
    if flip_rbt t2 t1 then (\<lambda>k v v'. f k v' v, t1, t2) else (f, t2, t1) in
    if small_rbt t2 then RBT_Impl.fold (rbt_comp_insert_with_key f) t2 t1
    else (case t1 of RBT_Impl.Empty \<Rightarrow> t2
      | RBT_Impl.Branch _ l1 a b r1 \<Rightarrow>
        case rbt_split_comp t2 a of (l2, \<beta>, r2) \<Rightarrow>
          rbt_join (rbt_comp_union_rec f l1 l2) a (case \<beta> of None \<Rightarrow> b | Some b' \<Rightarrow> f a b b') (rbt_comp_union_rec f r1 r2)))"
  by pat_completeness auto
termination
  using rbt_split_comp_size
  by (relation "measure (\<lambda>(f,t1,t2). size t1 + size t2)") (fastforce split: if_splits)+

declare rbt_comp_union_rec.simps[simp del]

function rbt_comp_union_swap_rec :: "('a \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> bool \<Rightarrow> ('a, 'b) rbt \<Rightarrow> ('a, 'b) rbt \<Rightarrow> ('a, 'b) rbt" where
  "rbt_comp_union_swap_rec f \<gamma> t1 t2 = (let (\<gamma>, t2, t1) =
    if flip_rbt t2 t1 then (\<not>\<gamma>, t1, t2) else (\<gamma>, t2, t1);
    f' = (if \<gamma> then (\<lambda>k v v'. f k v' v) else f) in
    if small_rbt t2 then RBT_Impl.fold (rbt_comp_insert_with_key f') t2 t1
    else case t1 of rbt.Empty \<Rightarrow> t2
      | Branch x l1 a b r1 \<Rightarrow>
        case rbt_split_comp t2 a of (l2, \<beta>, r2) \<Rightarrow>
          rbt_join (rbt_comp_union_swap_rec f \<gamma> l1 l2) a (case \<beta> of None \<Rightarrow> b | Some x \<Rightarrow> f' a b x) (rbt_comp_union_swap_rec f \<gamma> r1 r2))"
  by pat_completeness auto
termination
  using rbt_split_comp_size
  by (relation "measure (\<lambda>(f,\<gamma>,t1, t2). size t1 + size t2)") (fastforce split: if_splits)+

declare rbt_comp_union_swap_rec.simps[simp del]

lemma rbt_comp_union_swap_rec: "rbt_comp_union_swap_rec f \<gamma> t1 t2 =
  rbt_comp_union_rec (if \<gamma> then (\<lambda>k v v'. f k v' v) else f) t1 t2"
proof (induction f \<gamma> t1 t2 rule: rbt_comp_union_swap_rec.induct)
  case (1 f \<gamma> t1 t2)
  show ?case
    using 1[OF refl _ refl refl _ refl _ refl]
    unfolding rbt_comp_union_swap_rec.simps[of _ _ t1] rbt_comp_union_rec.simps[of _ t1]
    by (auto simp: Let_def split: rbt.splits prod.splits option.splits) (* slow *)
qed

lemma rbt_comp_union_swap_rec_code[code]: "rbt_comp_union_swap_rec f \<gamma> t1 t2 = (
    let bh1 = bheight t1; bh2 = bheight t2; (\<gamma>, t2, bh2, t1, bh1) =
    if bh1 < bh2 then (\<not>\<gamma>, t1, bh1, t2, bh2) else (\<gamma>, t2, bh2, t1, bh1);
    f' = (if \<gamma> then (\<lambda>k v v'. f k v' v) else f) in
    if bh2 < 4 then RBT_Impl.fold (rbt_comp_insert_with_key f') t2 t1
    else case t1 of rbt.Empty \<Rightarrow> t2
      | Branch x l1 a b r1 \<Rightarrow>
        case rbt_split_comp t2 a of (l2, \<beta>, r2) \<Rightarrow>
          rbt_join (rbt_comp_union_swap_rec f \<gamma> l1 l2) a (case \<beta> of None \<Rightarrow> b | Some x \<Rightarrow> f' a b x) (rbt_comp_union_swap_rec f \<gamma> r1 r2))"
  by (auto simp: rbt_comp_union_swap_rec.simps flip_rbt_def small_rbt_def)

definition "rbt_comp_union_with_key f t1 t2 = paint RBT_Impl.B (rbt_comp_union_swap_rec f False t1 t2)"

definition "map_filter_comp_inter f t1 t2 = List.map_filter (\<lambda>(k, v).
  case rbt_comp_lookup t1 k of None \<Rightarrow> None
  | Some v' \<Rightarrow> Some (k, f k v' v)) (RBT_Impl.entries t2)"

function rbt_comp_inter_rec :: "('a \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> ('a, 'b) rbt \<Rightarrow> ('a, 'b) rbt \<Rightarrow> ('a, 'b) rbt" where
  "rbt_comp_inter_rec f t1 t2 = (let (f, t2, t1) =
    if flip_rbt t2 t1 then (\<lambda>k v v'. f k v' v, t1, t2) else (f, t2, t1) in
    if small_rbt t2 then rbtreeify (map_filter_comp_inter f t1 t2)
    else case t1 of RBT_Impl.Empty \<Rightarrow> RBT_Impl.Empty
    | RBT_Impl.Branch _ l1 a b r1 \<Rightarrow>
      case rbt_split_comp t2 a of (l2, \<beta>, r2) \<Rightarrow> let l' = rbt_comp_inter_rec f l1 l2; r' = rbt_comp_inter_rec f r1 r2 in
      (case \<beta> of None \<Rightarrow> rbt_join2 l' r' | Some b' \<Rightarrow> rbt_join l' a (f a b b') r'))"
  by pat_completeness auto
termination
  using rbt_split_comp_size
  by (relation "measure (\<lambda>(f,t1,t2). size t1 + size t2)") (fastforce split: if_splits)+

declare rbt_comp_inter_rec.simps[simp del]

function rbt_comp_inter_swap_rec :: "('a \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> bool \<Rightarrow> ('a, 'b) rbt \<Rightarrow> ('a, 'b) rbt \<Rightarrow> ('a, 'b) rbt" where
  "rbt_comp_inter_swap_rec f \<gamma> t1 t2 = (let (\<gamma>, t2, t1) =
    if flip_rbt t2 t1 then (\<not>\<gamma>, t1, t2) else (\<gamma>, t2, t1);
    f' = if \<gamma> then (\<lambda>k v v'. f k v' v) else f in
    if small_rbt t2 then rbtreeify (map_filter_comp_inter f' t1 t2)
    else case t1 of rbt.Empty \<Rightarrow> rbt.Empty
    | Branch x l1 a b r1 \<Rightarrow>
      (case rbt_split_comp t2 a of (l2, \<beta>, r2) \<Rightarrow> let l' = rbt_comp_inter_swap_rec f \<gamma> l1 l2; r' = rbt_comp_inter_swap_rec f \<gamma> r1 r2 in
      (case \<beta> of None \<Rightarrow> rbt_join2 l' r' | Some b' \<Rightarrow> rbt_join l' a (f' a b b') r')))"
  by pat_completeness auto
termination
  using rbt_split_comp_size
  by (relation "measure (\<lambda>(f,\<gamma>,t1,t2). size t1 + size t2)") (fastforce split: if_splits)+

declare rbt_comp_inter_swap_rec.simps[simp del]

lemma rbt_comp_inter_swap_rec: "rbt_comp_inter_swap_rec f \<gamma> t1 t2 =
  rbt_comp_inter_rec (if \<gamma> then (\<lambda>k v v'. f k v' v) else f) t1 t2"
proof (induction f \<gamma> t1 t2 rule: rbt_comp_inter_swap_rec.induct)
  case (1 f \<gamma> t1 t2)
  show ?case
    using 1[OF refl _ refl refl _ refl _ refl]
    unfolding rbt_comp_inter_swap_rec.simps[of _ _ t1] rbt_comp_inter_rec.simps[of _ t1]
    by (auto simp: Let_def split: rbt.splits prod.splits option.splits)
qed

lemma comp_inter_with_key_code[code]: "rbt_comp_inter_swap_rec f \<gamma> t1 t2 = (
  let bh1 = bheight t1; bh2 = bheight t2; (\<gamma>, t2, bh2, t1, bh1) =
  if bh1 < bh2 then (\<not>\<gamma>, t1, bh1, t2, bh2) else (\<gamma>, t2, bh2, t1, bh1);
  f' = (if \<gamma> then (\<lambda>k v v'. f k v' v) else f) in
  if bh2 < 4 then rbtreeify (map_filter_comp_inter f' t1 t2)
  else case t1 of rbt.Empty \<Rightarrow> rbt.Empty
    | Branch x l1 a b r1 \<Rightarrow>
      (case rbt_split_comp t2 a of (l2, \<beta>, r2) \<Rightarrow> let l' = rbt_comp_inter_swap_rec f \<gamma> l1 l2; r' = rbt_comp_inter_swap_rec f \<gamma> r1 r2 in
      (case \<beta> of None \<Rightarrow> rbt_join2 l' r' | Some b' \<Rightarrow> rbt_join l' a (f' a b b') r')))"
  by (auto simp: rbt_comp_inter_swap_rec.simps flip_rbt_def small_rbt_def)

definition "rbt_comp_inter_with_key f t1 t2 = paint RBT_Impl.B (rbt_comp_inter_swap_rec f False t1 t2)"

definition "filter_comp_minus t1 t2 =
  filter (\<lambda>(k, _). rbt_comp_lookup t2 k = None) (RBT_Impl.entries t1)"

fun comp_minus :: "('a, 'b) rbt \<Rightarrow> ('a, 'b) rbt \<Rightarrow> ('a, 'b) rbt" where
  "comp_minus t1 t2 = (if small_rbt t2 then RBT_Impl.fold (\<lambda>k _ t. rbt_comp_delete k t) t2 t1
    else if small_rbt t1 then rbtreeify (filter_comp_minus t1 t2)
    else case t2 of RBT_Impl.Empty \<Rightarrow> t1
      | RBT_Impl.Branch _ l2 a b r2 \<Rightarrow>
        case rbt_split_comp t1 a of (l1, _, r1) \<Rightarrow> rbt_join2 (comp_minus l1 l2) (comp_minus r1 r2))"

declare comp_minus.simps[simp del]

definition "rbt_comp_minus t1 t2 = paint RBT_Impl.B (comp_minus t1 t2)"

context
  assumes c: "comparator c"
begin

lemma rbt_comp_lookup: "rbt_comp_lookup = ord.rbt_lookup (lt_of_comp c)" 
proof (intro ext)
  fix k and t :: "('a,'b)rbt"
  show "rbt_comp_lookup t k = ord.rbt_lookup (lt_of_comp c) t k"
    by (induct t, unfold rbt_comp_lookup.simps ord.rbt_lookup.simps
      comparator.two_comparisons_into_case_order[OF c]) 
      (auto split: order.splits)
qed  

lemma rbt_comp_ins: "rbt_comp_ins = ord.rbt_ins (lt_of_comp c)" 
proof (intro ext)
  fix f k v and t :: "('a,'b)rbt"
  show "rbt_comp_ins f k v t = ord.rbt_ins (lt_of_comp c) f k v t"
    by (induct f k v t rule: rbt_comp_ins.induct, unfold rbt_comp_ins.simps ord.rbt_ins.simps
      comparator.two_comparisons_into_case_order[OF c]) 
      (auto split: order.splits)
qed  

lemma rbt_comp_insert_with_key: "rbt_comp_insert_with_key = ord.rbt_insert_with_key (lt_of_comp c)"
  unfolding rbt_comp_insert_with_key_def[abs_def] ord.rbt_insert_with_key_def[abs_def]
  unfolding rbt_comp_ins ..

lemma rbt_comp_insert: "rbt_comp_insert = ord.rbt_insert (lt_of_comp c)"
  unfolding rbt_comp_insert_def[abs_def] ord.rbt_insert_def[abs_def]
  unfolding rbt_comp_insert_with_key ..

lemma rbt_comp_del: "rbt_comp_del = ord.rbt_del (lt_of_comp c)" 
proof - {
  fix k a b and s t :: "('a,'b)rbt"
  have 
    "rbt_comp_del_from_left k t a b s = ord.rbt_del_from_left (lt_of_comp c) k t a b s"
    "rbt_comp_del_from_right k t a b s = ord.rbt_del_from_right (lt_of_comp c) k t a b s"
    "rbt_comp_del k t = ord.rbt_del (lt_of_comp c) k t"
  by (induct k t a b s and k t a b s and k t rule: rbt_comp_del_from_left_rbt_comp_del_from_right_rbt_comp_del.induct,
    unfold 
      rbt_comp_del.simps ord.rbt_del.simps
      rbt_comp_del_from_left.simps ord.rbt_del_from_left.simps
      rbt_comp_del_from_right.simps ord.rbt_del_from_right.simps
      comparator.two_comparisons_into_case_order[OF c],
    auto split: order.split) 
  }
  thus ?thesis by (intro ext)
qed  

lemma rbt_comp_delete: "rbt_comp_delete = ord.rbt_delete (lt_of_comp c)"
  unfolding rbt_comp_delete_def[abs_def] ord.rbt_delete_def[abs_def]
  unfolding rbt_comp_del ..

lemma rbt_comp_bulkload: "rbt_comp_bulkload = ord.rbt_bulkload (lt_of_comp c)"
  unfolding rbt_comp_bulkload_def[abs_def] ord.rbt_bulkload_def[abs_def]
  unfolding rbt_comp_insert ..

lemma rbt_comp_map_entry: "rbt_comp_map_entry = ord.rbt_map_entry (lt_of_comp c)" 
proof (intro ext)
  fix f k and t :: "('a,'b)rbt"
  show "rbt_comp_map_entry f k t = ord.rbt_map_entry (lt_of_comp c) f k t"
    by (induct t, unfold rbt_comp_map_entry.simps ord.rbt_map_entry.simps
      comparator.two_comparisons_into_case_order[OF c]) 
      (auto split: order.splits)
qed  

lemma comp_sunion_with: "comp_sunion_with = ord.sunion_with (lt_of_comp c)"
proof (intro ext)
  fix f and as bs :: "('a \<times> 'b)list"
  show "comp_sunion_with f as bs = ord.sunion_with (lt_of_comp c) f as bs"
    by (induct f as bs rule: comp_sunion_with.induct,
      unfold comp_sunion_with.simps ord.sunion_with.simps
      comparator.two_comparisons_into_case_order[OF c]) 
      (auto split: order.splits)
qed

lemma anti_sym: "lt_of_comp c a x \<Longrightarrow> lt_of_comp c x a \<Longrightarrow> False"
  by (metis c comparator.Gt_lt_conv comparator.Lt_lt_conv order.distinct(5))

lemma rbt_split_comp: "rbt_split_comp t x = ord.rbt_split (lt_of_comp c) t x"
  by (induction t x rule: rbt_split_comp.induct)
     (auto simp: ord.rbt_split.simps comparator.le_lt_convs[OF c]
      split: order.splits prod.splits dest: anti_sym)

lemma comp_union_with_key: "rbt_comp_union_rec f t1 t2 = ord.rbt_union_rec (lt_of_comp c) f t1 t2"
proof (induction f t1 t2 rule: rbt_comp_union_rec.induct)
  case (1 f t1 t2)
  obtain f' t1' t2' where flip: "(f', t2', t1') =
    (if flip_rbt t2 t1 then (\<lambda>k v v'. f k v' v, t1, t2) else (f, t2, t1))"
    by fastforce
  show ?case
  proof (cases t1')
    case (Branch _ l1 a b r1)
    have t1_not_Empty: "t1' \<noteq> RBT_Impl.Empty"
      by (auto simp: Branch)
    obtain l2 \<beta> r2 where split: "rbt_split_comp t2' a = (l2, \<beta>, r2)"
      by (cases "rbt_split_comp t2' a") auto
    show ?thesis
      using 1[OF flip refl _ _ Branch]
      unfolding rbt_comp_union_rec.simps[of _ t1] ord.rbt_union_rec.simps[of _ _ t1] flip[symmetric]
      by (auto simp: Branch split rbt_split_comp[symmetric] rbt_comp_insert_with_key
          split: prod.splits)
  qed (auto simp: rbt_comp_union_rec.simps[of _ t1] ord.rbt_union_rec.simps[of _ _ t1] flip[symmetric]
       rbt_comp_insert_with_key rbt_split_comp[symmetric])
qed

lemma comp_sinter_with: "comp_sinter_with = ord.sinter_with (lt_of_comp c)"
proof (intro ext)
  fix f and as bs :: "('a \<times> 'b)list"
  show "comp_sinter_with f as bs = ord.sinter_with (lt_of_comp c) f as bs"
    by (induct f as bs rule: comp_sinter_with.induct,
      unfold comp_sinter_with.simps ord.sinter_with.simps
      comparator.two_comparisons_into_case_order[OF c]) 
      (auto split: order.splits)
qed

lemma rbt_comp_union_with_key: "rbt_comp_union_with_key = ord.rbt_union_with_key (lt_of_comp c)"
  by (rule ext)+
     (auto simp: rbt_comp_union_with_key_def rbt_comp_union_swap_rec ord.rbt_union_with_key_def
      ord.rbt_union_swap_rec comp_union_with_key)

lemma comp_inter_with_key: "rbt_comp_inter_rec f t1 t2 = ord.rbt_inter_rec (lt_of_comp c) f t1 t2"
proof (induction f t1 t2 rule: rbt_comp_inter_rec.induct)
  case (1 f t1 t2)
  obtain f' t1' t2' where flip: "(f', t2', t1') =
    (if flip_rbt t2 t1 then (\<lambda>k v v'. f k v' v, t1, t2) else (f, t2, t1))"
    by fastforce
  show ?case
  proof (cases t1')
    case (Branch _ l1 a b r1)
    have t1_not_Empty: "t1' \<noteq> RBT_Impl.Empty"
      by (auto simp: Branch)
    obtain l2 \<beta> r2 where split: "rbt_split_comp t2' a = (l2, \<beta>, r2)"
      by (cases "rbt_split_comp t2' a") auto
    show ?thesis
      using 1[OF flip refl _ _ Branch]
      unfolding rbt_comp_inter_rec.simps[of _ t1] ord.rbt_inter_rec.simps[of _ _ t1] flip[symmetric]
      by (auto simp: Branch split rbt_split_comp[symmetric] rbt_comp_lookup
          ord.map_filter_inter_def map_filter_comp_inter_def split: prod.splits)
  qed (auto simp: rbt_comp_inter_rec.simps[of _ t1] ord.rbt_inter_rec.simps[of _ _ t1] flip[symmetric]
       ord.map_filter_inter_def map_filter_comp_inter_def rbt_comp_lookup rbt_split_comp[symmetric])
qed

lemma rbt_comp_inter_with_key: "rbt_comp_inter_with_key = ord.rbt_inter_with_key (lt_of_comp c)"
  by (rule ext)+
     (auto simp: rbt_comp_inter_with_key_def rbt_comp_inter_swap_rec
      ord.rbt_inter_with_key_def ord.rbt_inter_swap_rec comp_inter_with_key)

lemma comp_minus: "comp_minus t1 t2 = ord.rbt_minus_rec (lt_of_comp c) t1 t2"
proof (induction t1 t2 rule: comp_minus.induct)
  case (1 t1 t2)
  show ?case
  proof (cases t2)
    case (Branch _ l2 a u r2)
    have t2_not_Empty: "t2 \<noteq> RBT_Impl.Empty"
      by (auto simp: Branch)
    obtain l1 \<beta> r1 where split: "rbt_split_comp t1 a = (l1, \<beta>, r1)"
      by (cases "rbt_split_comp t1 a") auto
    show ?thesis
      using 1[OF _ _ Branch]
      unfolding comp_minus.simps[of t1 t2] ord.rbt_minus_rec.simps[of _ t1 t2]
      by (auto simp: Branch split rbt_split_comp[symmetric] rbt_comp_delete rbt_comp_lookup
          filter_comp_minus_def ord.filter_minus_def split: prod.splits)
  qed (auto simp: comp_minus.simps[of t1] ord.rbt_minus_rec.simps[of _ t1]
       filter_comp_minus_def ord.filter_minus_def
       rbt_comp_delete rbt_comp_lookup rbt_split_comp[symmetric])
qed

lemma rbt_comp_minus: "rbt_comp_minus = ord.rbt_minus (lt_of_comp c)"
  by (rule ext)+ (auto simp: rbt_comp_minus_def ord.rbt_minus_def comp_minus)

lemmas rbt_comp_simps = 
  rbt_comp_insert
  rbt_comp_lookup
  rbt_comp_delete
  rbt_comp_bulkload
  rbt_comp_map_entry
  rbt_comp_union_with_key
  rbt_comp_inter_with_key
  rbt_comp_minus
end
end

end
