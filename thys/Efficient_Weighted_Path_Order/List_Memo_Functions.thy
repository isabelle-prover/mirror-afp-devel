section \<open>Memoized Functions on Lists\<close>

text \<open>We define memoized version of lexicographic comparison of lists, 
  multiset comparison of lists, filter on lists, etc.\<close>

theory List_Memo_Functions
  imports 
    Indexed_Term
    Knuth_Bendix_Order.Lexicographic_Extension
    Weighted_Path_Order.Multiset_Extension2_Impl
    "HOL-Library.Mapping" 
begin



definition valid_memory :: "('a \<Rightarrow> 'b) \<Rightarrow> ('i \<Rightarrow> 'a) \<Rightarrow> ('i, 'b) mapping \<Rightarrow> bool"
  where
    "valid_memory f ind mem = (\<forall> i b. Mapping.lookup mem i = Some b \<longrightarrow> f (ind i) = b)"

definition memoize_fun where "memoize_fun impl f g ind A =
  ((\<forall> x m p m'. valid_memory f ind m \<longrightarrow> impl m x = (p,m') \<longrightarrow> x \<in> A \<longrightarrow> 
        p = f (g x) \<and> valid_memory f ind m'))" 

lemma memoize_funD: assumes "memoize_fun impl f g ind A" 
  shows "valid_memory f ind m \<Longrightarrow>  impl m x = (p,m') \<Longrightarrow> x \<in> A \<Longrightarrow> p = f (g x) \<and> valid_memory f ind m'" 
  using assms unfolding memoize_fun_def by auto

lemma memoize_funI: assumes "\<And> m x p m'. valid_memory f ind m \<Longrightarrow> impl m x = (p,m') \<Longrightarrow> x \<in> A \<Longrightarrow> p = f (g x) \<and> valid_memory f ind m'" 
  shows "memoize_fun impl f g ind A" 
  using assms unfolding memoize_fun_def by auto

lemma memoize_fun_pairI: assumes "\<And> m x y p m'. valid_memory f ind m \<Longrightarrow> impl m (x,y) = (p,m') \<Longrightarrow> x \<in> A \<Longrightarrow> y \<in> B \<Longrightarrow> p = f (g x, h y) \<and> valid_memory f ind m'" 
  shows "memoize_fun impl f (map_prod g h) ind (A \<times> B)" 
  using assms unfolding memoize_fun_def by auto

lemma memoize_fun_mono: assumes "memoize_fun impl f g ind B"
  and "A \<subseteq> B" 
shows "memoize_fun impl f g ind A" 
  using assms unfolding memoize_fun_def by blast


fun filter_mem :: "('a \<Rightarrow> 'b) \<Rightarrow> ('m \<Rightarrow> 'b \<Rightarrow> 'c \<times> 'm) \<Rightarrow> ('c \<Rightarrow> bool) \<Rightarrow> 'm \<Rightarrow> 'a list \<Rightarrow> ('a list \<times> 'm)"
  where
    "filter_mem pre f post mem [] = ([], mem)" 
  | "filter_mem pre f post mem (x # xs) = (case f mem (pre x) of 
     (c,mem') \<Rightarrow> case filter_mem pre f post mem' xs of 
       (ys, mem'') \<Rightarrow> (if post c then (x # ys, mem'') else (ys, mem'')))" 

fun forall_mem :: "('a \<Rightarrow> 'b) \<Rightarrow> ('m \<Rightarrow> 'b \<Rightarrow> 'c \<times> 'm) \<Rightarrow> ('c \<Rightarrow> bool) \<Rightarrow> 'm \<Rightarrow> 'a list \<Rightarrow> bool \<times> 'm"
  where
    "forall_mem pre f post mem [] = (True, mem)"
  | "forall_mem pre f post mem (x # xs) = (case f mem (pre x) of (c, mem')
      \<Rightarrow> if post c then forall_mem pre f post mem' xs else (False, mem'))"

fun exists_mem :: "('a \<Rightarrow> 'b) \<Rightarrow> ('m \<Rightarrow> 'b \<Rightarrow> ('c \<times> 'm)) \<Rightarrow> ('c \<Rightarrow> bool) \<Rightarrow> 'm \<Rightarrow> 'a list \<Rightarrow> (bool \<times> 'm)"
  where
    "exists_mem pre f post mem [] = (False, mem)"
  | "exists_mem pre f post mem (x # xs) = (case f mem (pre x) of (c, mem')
      \<Rightarrow> if post c then (True, mem') else exists_mem pre f post mem' xs)"

type_synonym term_rel_mem = "(index \<times> index, bool \<times> bool) mapping"
type_synonym 'a term_rel_mem_type = "term_rel_mem \<Rightarrow> 'a \<times> 'a \<Rightarrow> (bool \<times> bool) \<times> term_rel_mem"

fun lex_ext_unbounded_mem :: "'a term_rel_mem_type \<Rightarrow> term_rel_mem \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> (bool \<times> bool) \<times> term_rel_mem"
  where "lex_ext_unbounded_mem f mem [] [] = ((False, True), mem)" |
    "lex_ext_unbounded_mem f mem (_ # _) [] = ((True, True), mem)" |
    "lex_ext_unbounded_mem f mem [] (_ # _) = ((False, False), mem)" |
    "lex_ext_unbounded_mem f mem (a # as) (b # bs) =
      (let (sns_res, mem_new) = f mem (a,b) in
        (case sns_res of
          (True, _) \<Rightarrow> ((True, True), mem_new)
        | (False, True) \<Rightarrow> lex_ext_unbounded_mem f mem_new as bs
        | (False, False) \<Rightarrow> ((False, False), mem_new)
        )
      )"

lemma filter_mem_len: "filter_mem pre f post mem xs = (ys,mem') \<Longrightarrow> length ys \<le> length xs"
  by (induction xs arbitrary: mem ys mem'; force split: prod.splits if_splits)

lemma filter_mem_len2: "(ys,mem') = filter_mem mem pre f post xs \<Longrightarrow> length ys \<le> length xs"
  using filter_mem_len[of mem pre f post xs ys mem'] by auto

lemma filter_mem_set: "filter_mem pre f post mem xs = (ys,mem') \<Longrightarrow> set ys \<subseteq> set xs"
  by (induction xs arbitrary: mem ys mem', auto split: prod.splits if_splits) blast

function mul_ext_mem :: "'a term_rel_mem_type \<Rightarrow> term_rel_mem \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> (bool \<times> bool) \<times> term_rel_mem"
  and mul_ext_dom_mem :: "'a term_rel_mem_type \<Rightarrow> term_rel_mem \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> (bool \<times> bool) \<times> term_rel_mem"
  where
    "mul_ext_mem f mem [] [] = ((False, True), mem)"
  | "mul_ext_mem f mem [] (v # va) = ((False, False), mem)"
  | "mul_ext_mem f mem (v # va) [] = ((True, True), mem)"
  | "mul_ext_mem f mem (v # va) (y # ys) = mul_ext_dom_mem f mem (v # va) [] y ys"
  | "mul_ext_dom_mem f mem [] xs y ys = ((False, False), mem)"
  | "mul_ext_dom_mem f mem (x # xsa) xs y ys =
      (case f mem (x,y) of (sns_res, mem_new_1) \<Rightarrow>
        (case sns_res of
          (True, _) \<Rightarrow> (case
              (filter_mem (Pair x) f (\<lambda> p. \<not> fst p) mem_new_1 ys) 
                of  (ys_new, mem_new_2) \<Rightarrow> case
               mul_ext_mem f mem_new_2 (xsa @ xs) ys_new of (tmp_res, mem_new_3) \<Rightarrow>
              if snd tmp_res
              then ((True, True), mem_new_3)
              else mul_ext_dom_mem f mem_new_3 xsa (x # xs) y ys)
        | (False, True) \<Rightarrow> (case mul_ext_mem f mem_new_1 (xsa @ xs) ys of 
              (sns_res_a, mem_new_2) \<Rightarrow> case mul_ext_dom_mem f mem_new_2 xsa (x # xs) y ys of
              (sns_res_b, mem_new_3) \<Rightarrow>
              (or2 sns_res_a sns_res_b, mem_new_3))
        | (False, False) \<Rightarrow> mul_ext_dom_mem f mem_new_1 xsa (x # xs) y ys))"
  by pat_completeness auto

termination by (relation "measures [ 
   (\<lambda> input. case input of Inl (_, _, xs, ys) \<Rightarrow> length ys | Inr (_, _, xs, xs', y, ys) \<Rightarrow> length ys),
   (\<lambda> input. case input of Inl (_, _, xs, ys) \<Rightarrow> 0 | Inr (_, _, xs, xs', y, ys) \<Rightarrow> Suc (length xs))
  ]")
      (auto dest: filter_mem_len2)

subsection \<open>Congruence Rules\<close>

lemma filter_mem_cong[fundef_cong]: 
  assumes "\<And> m x. x \<in> set xs \<Longrightarrow> f m (pre x) = g m (pre x)" 
  shows "filter_mem pre f post mem xs = filter_mem pre g post mem xs" 
  using assms by (induct xs arbitrary: mem, auto split: prod.splits)


lemma forall_mem_cong[fundef_cong]: 
  assumes "\<And> m x. x \<in> set xs \<Longrightarrow> f m (pre x) = g m (pre x)" 
  shows "forall_mem pre f post mem xs = forall_mem pre g post mem xs" 
  using assms by (induct xs arbitrary: mem, auto split: prod.splits)

lemma exists_mem_cong[fundef_cong]: 
  assumes "\<And> m x. x \<in> set xs \<Longrightarrow> f m (pre x) = g m (pre x)" 
  shows "exists_mem pre f post mem xs = exists_mem pre g post mem xs" 
  using assms by (induct xs arbitrary: mem, auto split: prod.splits)

lemma lex_ext_unbounded_mem_cong[fundef_cong]:
  assumes "\<And>x y m. x \<in> set xs \<Longrightarrow> y \<in> set ys \<Longrightarrow> f m (x,y) = g m (x,y)"
  shows "lex_ext_unbounded_mem f m xs ys = lex_ext_unbounded_mem g m xs ys"
  using assms 
  by (induct f m xs ys rule: lex_ext_unbounded_mem.induct, 
      auto split: prod.splits bool.splits)

lemma mul_ext_mem_cong[fundef_cong]:
  assumes "\<And>x y m. x \<in> set xs \<Longrightarrow> y \<in> set ys \<Longrightarrow> f m (x,y) = g m (x,y)"
  shows "mul_ext_mem f m xs ys = mul_ext_mem g m xs ys"
proof -
  have "(\<And>x' y' m. x' \<in> set xs \<Longrightarrow> y' \<in> set ys \<Longrightarrow> f m (x',y') = g m (x', y')) \<Longrightarrow>
        mul_ext_mem f m xs ys = mul_ext_mem g m xs ys"
    "(\<And>x' y' m. x' \<in> set (xs @ xs') \<Longrightarrow> y' \<in> set (y # ys) \<Longrightarrow> f m (x', y') = g m (x', y')) \<Longrightarrow>
        mul_ext_dom_mem f m xs xs' y ys = mul_ext_dom_mem g m xs xs' y ys" for xs' y
  proof (induct g m xs ys and g m xs xs' y ys rule: mul_ext_mem_mul_ext_dom_mem.induct)
    case (6 g m x xs xs' y ys)
    note IHs = 6(1-5)
    note fg = 6(6)
    note [simp del] = mul_ext_mem.simps mul_ext_dom_mem.simps
    note [simp] = mul_ext_dom_mem.simps(2)[of _ m x xs xs' y ys]
    from fg have fgx[simp]: "f m (x, y) = g m (x, y)" by simp
    obtain a1 b1 m1 where r1[simp]: "g m (x, y) = ((a1,b1),m1)" by (cases "g m (x,y)", auto)
    note IHs = IHs(1-5)[OF r1[symmetric] refl]
    show ?case 
    proof (cases a1)
      case True
      hence "a1 = True" by auto
      note IHs = IHs(1-2)[OF this]
      let ?rec = "filter_mem (Pair x) g (\<lambda> p. \<not> fst p) m1 ys" 
      let ?recf = "filter_mem (Pair x) f (\<lambda> p. \<not> fst p) m1 ys" 
      have [simp]: "?recf = ?rec" 
        by (rule filter_mem_cong, insert fg, auto)
      obtain zs m2 where rec: "?rec = (zs,m2)" by fastforce
      from filter_mem_set[OF rec] have sub: "set zs \<subseteq> set ys" by auto
      note IHs = IHs(1-2)[OF rec[symmetric]]
      have IH1[simp]: "mul_ext_mem f m2 (xs @ xs') zs = mul_ext_mem g m2 (xs @ xs') zs" 
        by (rule IHs(1), rule fg) (insert sub, auto)
      obtain p3 m3 where rec2[simp]: "mul_ext_mem g m2 (xs @ xs') zs = (p3,m3)" by fastforce
      note IHs(2)[OF rec2[symmetric] _ fg]
      thus ?thesis using True by (simp add: rec)
    next
      case False
      hence "a1 = False" by simp
      note IHs = IHs(3-)[OF this]
      show ?thesis 
      proof (cases b1)
        case True
        hence "b1 = True" by simp
        note IHs = IHs(1-2)[OF this]
        have [simp]: "mul_ext_mem f m1 (xs @ xs') ys = mul_ext_mem g m1 (xs @ xs') ys" 
          by (rule IHs(1)[OF fg], auto)
        obtain p2 m2 where rec1[simp]: "mul_ext_mem g m1 (xs @ xs') ys = (p2,m2)" by fastforce
        have [simp]: "mul_ext_dom_mem f m2 xs (x # xs') y ys = mul_ext_dom_mem g m2 xs (x # xs') y ys" 
          by (rule IHs(2)[OF rec1[symmetric] fg], auto)
        show ?thesis using False True by simp
      next
        case b1: False
        hence "b1 = False" by simp
        note IHs = IHs(3)[OF this fg]
        have [simp]: "mul_ext_dom_mem f m1 xs (x # xs') y ys = mul_ext_dom_mem g m1 xs (x # xs') y ys" 
          by (rule IHs, auto)
        show ?thesis using False b1 by auto
      qed
    qed
  qed auto
  with assms show ?thesis by auto
qed

subsection \<open>Connection to Original Functions\<close>

lemma filter_mem: assumes "valid_memory fun ind mem1" 
  "filter_mem f fun_mem h mem1 xs = (ys, mem2)" 
  "memoize_fun fun_mem fun g ind (f ` set xs)" 
shows "ys = filter (\<lambda>y. h (fun (g (f y)))) xs \<and> valid_memory fun ind mem2" 
  using assms
proof (induct xs arbitrary: mem1 ys mem2)
  case (Cons x xs mem1 ys mem')
  note res = Cons(3)
  note mem1 = Cons(2)
  note fun_mems = Cons(4)
  obtain p mem2 where fm: "fun_mem mem1 (f x) = (p, mem2)" by force  
  from memoize_funD[OF fun_mems mem1 fm]
  have p: "p = fun (g (f x))" and mem2: "valid_memory fun ind mem2" by auto
  note res = res[unfolded filter_mem.simps fm split]
  obtain zs mem3 where rec: "filter_mem f fun_mem h mem2 xs = (zs, mem3)" by force
  note res = res[unfolded rec split]
  from Cons(1)[OF mem2 rec memoize_fun_mono[OF fun_mems]] 
  have mem3: "valid_memory fun ind mem3" and zs: "zs = filter (\<lambda>y. h (fun (g (f y)))) xs" by auto
  from mem3 res
  show ?case unfolding zs p by auto
qed auto

lemma forall_mem: assumes "valid_memory fun ind m" 
  and "forall_mem f fun_mem h m xs = (b, m')" 
  and "memoize_fun fun_mem fun g ind (f ` set xs)"
shows "b = Ball (set xs) (\<lambda>s. h (fun (g (f s)))) \<and> valid_memory fun ind m'" 
  using assms
proof (induct xs arbitrary: m b m')
  case (Cons x xs m b m')
  obtain b1 m1 where x: "fun_mem m (f x) = (b1,m1)" by force
  note res = Cons(3)[unfolded forall_mem.simps x map_prod_simp split]
  note mem = Cons(2)
  from memoize_funD[OF Cons(4) mem x]
  have b1: "b1 = fun (g (f x))" and m1: "valid_memory fun ind m1"   by auto
  obtain b2 m2 where rec: "forall_mem f fun_mem h m1 xs = (b2,m2)" by fastforce
  from Cons(1)[OF m1 rec memoize_fun_mono[OF Cons(4)]] 
  have IH: "b2 = Ball (set xs) (\<lambda>s. h (fun (g (f s))))" and m2: "valid_memory fun ind m2" by auto
  show ?case using res rec IH m2 b1 m1 by (auto split: if_splits)
qed auto

lemma exists_mem: assumes "valid_memory fun ind m" 
  and "exists_mem f fun_mem h m xs = (b, m')" 
  and "memoize_fun fun_mem fun g ind (f ` set xs)"
shows "b = Bex (set xs) (\<lambda>s. h (fun (g (f s)))) \<and> valid_memory fun ind m'" 
  using assms
proof (induct xs arbitrary: m b m')
  case (Cons x xs m b m')
  obtain b1 m1 where x: "fun_mem m (f x) = (b1,m1)" by force
  note res = Cons(3)[unfolded exists_mem.simps x map_prod_simp split]
  note mem = Cons(2)
  from memoize_funD[OF Cons(4) mem x]
  have b1: "b1 = fun (g (f x))" and m1: "valid_memory fun ind m1"   by auto
  obtain b2 m2 where rec: "exists_mem f fun_mem h m1 xs = (b2,m2)" by fastforce
  from Cons(1)[OF m1 rec memoize_fun_mono[OF Cons(4)]] 
  have IH: "b2 = Bex (set xs) (\<lambda>s. h (fun (g (f s))))" and m2: "valid_memory fun ind m2" by auto
  show ?case using res rec IH m2 b1 m1 by (auto split: if_splits)
qed auto

lemma lex_ext_unbounded_mem: assumes "rel_pair = (\<lambda>(s, t). rel s t)" 
  shows "valid_memory rel_pair ind mem \<Longrightarrow> lex_ext_unbounded_mem rel_mem mem xs ys = (p, mem')
  \<Longrightarrow> memoize_fun rel_mem rel_pair (map_prod g h) ind (set xs \<times> set ys) 
  \<Longrightarrow> p = lex_ext_unbounded rel (map g xs) (map h ys) \<and> valid_memory rel_pair ind mem'" 
proof (induct rel_mem mem xs ys arbitrary: p mem' rule: lex_ext_unbounded_mem.induct)
  case (4 rel_mem mem x xs y ys)
  note lex_ext_unbounded.simps[simp]
  note IH = 4(1)[OF refl _ refl]
  obtain s ns mem1 where impl: "rel_mem mem (x, y) = ((s,ns), mem1)" by (cases "rel_mem mem (x, y)", auto)
  have rel: "rel (g x) (h y) = (s,ns)" and mem1: "valid_memory rel_pair ind mem1" 
    using memoize_funD[OF 4(4,2) impl] assms impl unfolding assms o_def by auto 
  note res = 4(3)[unfolded lex_ext_unbounded_mem.simps Let_def impl split]
  have rel_pair: "lex_ext_unbounded rel (map g (x # xs)) (map h (y # ys)) = (
       if s then (True, True) else if ns then lex_ext_unbounded rel (map g xs) (map h ys) else (False, False))" 
    unfolding lex_ext_unbounded.simps list.simps Let_def split rel by simp  
  show ?case 
  proof (cases "s \<or> \<not> ns")
    case True
    thus ?thesis using res rel_pair mem1 by auto
  next
    case False
    obtain p2 mem2 where rec: "lex_ext_unbounded_mem rel_mem mem1 xs ys = (p2, mem2)" by fastforce
    from False have "s = False" "ns = True" by auto
    from IH[unfolded impl, OF refl this mem1 rec memoize_fun_mono[OF 4(4)]]
    have mem2: "valid_memory rel_pair ind mem2" and p2: "p2 = lex_ext_unbounded rel (map g xs) (map h ys)" by auto
    show ?thesis unfolding rel_pair using res rec False mem2 p2 by (auto split: if_splits)
  qed
qed (auto simp: lex_ext_unbounded.simps)

lemma mul_ext_mem: assumes "rel_pair = (\<lambda>(s, t). rel s t)" 
  shows "valid_memory rel_pair ind mem \<Longrightarrow> mul_ext_mem rel_mem mem xs ys = (p, mem')
  \<Longrightarrow> memoize_fun rel_mem rel_pair (map_prod g h) ind (set xs \<times> set ys) 
  \<Longrightarrow> p = mul_ext_impl rel (map g xs) (map h ys) \<and> valid_memory rel_pair ind mem'" (is "?A \<Longrightarrow> ?B \<Longrightarrow> ?C \<Longrightarrow> ?D")
proof -
  have "?A \<Longrightarrow> ?B \<Longrightarrow> ?C \<Longrightarrow> ?D"
    "valid_memory rel_pair ind mem \<Longrightarrow> mul_ext_dom_mem rel_mem mem xs xs' y ys = (p, mem')
  \<Longrightarrow> memoize_fun rel_mem rel_pair (map_prod g h) ind (set (xs @ xs') \<times> set (y # ys)) 
  \<Longrightarrow> p = mul_ex_dom rel (map g xs) (map g xs') (h y) (map h ys) \<and> valid_memory rel_pair ind mem'"
    for xs' y
  proof (induct rel_mem mem xs ys and rel_mem mem xs xs' y ys arbitrary: p mem' and p mem' rule: mul_ext_mem_mul_ext_dom_mem.induct)
    case (6 sns mem x xs ys d zs pair mem')  
    note IHs = 6(1-5)
    note mem = 6(6)
    note res = 6(7)
    note memo = 6(8)
    let ?Sns = "\<lambda> x. rel_pair (map_prod g h x)" 
    let ?xd = "rel_pair (g x, h d)"   
    obtain p1 mem1 where sns: "sns mem (x,d) = (p1, mem1)" by fastforce
    note IHs = IHs[OF sns[symmetric]]
    from memoize_funD[OF memo mem sns]
    have p1: "p1 = ?xd" and mem1: "valid_memory rel_pair ind mem1" by auto
    note sns = sns[unfolded p1]
    note res = res[unfolded mul_ext_dom_mem.simps sns split]
    have rel: "rel (g x) (h d) = ?xd" unfolding assms by auto
    define wp where "wp = mul_ex_dom rel (map g (x # xs)) (map g ys) (h d) (map h zs)" 
    note wp = wp_def[unfolded list.simps, unfolded mul_ex_dom.simps rel]
    consider (1) b where "?xd = (True,b)" | (2) "?xd = (False,True)" | (3) "?xd = (False,False)" 
      by (cases ?xd, auto)
    hence "valid_memory rel_pair ind mem' \<and> pair = wp" 
    proof cases
      case (1 b)
      let ?pre = "Pair x" 
      let ?post = "(\<lambda> p. \<not> fst p)" 
      from 1 p1 have "(True, b) = p1" by auto
      note IHs = IHs(1-2)[OF this, OF refl]
      obtain p2 mem2 where filter: "filter_mem ?pre sns ?post mem1 zs = (p2, mem2)" by force
      obtain p3 mem3 where rec1: "mul_ext_mem sns mem2 (xs @ ys) p2 = (p3,mem3)" by fastforce
      obtain p4 mem4 where rec2: "mul_ext_dom_mem sns mem3 xs (x # ys) d zs = (p4, mem4)" by fastforce
      note res = res[unfolded 1 split[of _ _ mem1], unfolded Let_def split, simplified, unfolded filter rec1 split rec2]
      note wp = wp[unfolded 1 split bool.simps]
      {
        fix z
        assume "z \<in> set zs" 
        hence "(x,z) \<in> set ((x # xs) @ ys) \<times> set (d # zs)" by auto
        from memoize_funD[OF memo _ _ this]
        have "valid_memory rel_pair ind m \<Longrightarrow> sns m (x, z) = (p, m') \<Longrightarrow> p = rel_pair (map_prod g h (x, z)) \<and> valid_memory rel_pair ind m'" 
          for m p m' by auto
      }
      hence "memoize_fun sns rel_pair (map_prod g h) ind (Pair x ` set zs)" 
        by (intro memoize_funI, blast)
      from filter_mem[OF mem1 filter, of "map_prod g h",
          OF this]
      have mem2: "valid_memory rel_pair ind mem2" and p2: "p2 = filter (\<lambda>y. \<not> fst (rel_pair (g x, h y))) zs"   
        by auto
      have "filter (\<lambda>y. \<not> fst (rel (g x) y)) (map h zs) = map h p2" unfolding p2 assms split 
        by (induct zs, auto)
      note wp = wp[unfolded this]
      note IHs = IHs[OF filter[symmetric]]
      from IHs(1)[OF mem2 rec1 memoize_fun_mono[OF memo]] p2
      have mem3: "valid_memory rel_pair ind mem3" 
        and p3: "p3 = mul_ext_impl rel (map g xs @ map g ys) (map h p2)" 
        by auto  
      note wp = wp[folded p3]
      show ?thesis 
      proof (cases "snd p3")
        case True
        thus ?thesis using res wp mem3 by auto
      next
        case False
        with IHs(2)[OF rec1[symmetric] False mem3 rec2 memoize_fun_mono[OF memo]] wp res
        show ?thesis by auto
      qed
    next  
      case 2
      note wp = wp[unfolded 2 split bool.simps]
      obtain p2 mem2 where rec2: "mul_ext_mem sns mem1 (xs @ ys) zs = (p2, mem2)" by fastforce
      obtain p3 mem3 where rec3: "mul_ext_dom_mem sns mem2 xs (x # ys) d zs = (p3, mem3)" by fastforce
      from 2 p1 have "(False, True) = p1" by auto
      note IHs = IHs(3-4)[OF this refl refl, unfolded rec2]
      from IHs(1)[OF mem1 refl memoize_fun_mono[OF memo]] 
      have mem2: "valid_memory rel_pair ind mem2" and p2: "p2 = mul_ext_impl rel (map g (xs @ ys)) (map h zs)" 
        by auto
      from IHs(2)[OF refl mem2 rec3 memoize_fun_mono[OF memo]]
      have mem3: "valid_memory rel_pair ind mem3" and p3: "p3 = mul_ex_dom rel (map g xs) (map g (x # ys)) (h d) (map h zs)" by auto
      from wp res[unfolded Let_def split 2 bool.simps rec2 rec3]
      show ?thesis using mem3 p2 p3 by auto
    next
      case 3
      obtain p2 mem2 where rec2: "mul_ext_dom_mem sns mem1 xs (x # ys) d zs = (p2,mem2)" by fastforce
      from 3 p1 have "(False, False) = p1" by auto
      from IHs(5)[OF this refl refl mem1 rec2 memoize_fun_mono[OF memo]]
      have mem2: "valid_memory rel_pair ind mem2" and p2: "p2 = mul_ex_dom rel (map g xs) (map g (x # ys)) (h d) (map h zs)" 
        by auto
      have "wp = p2" unfolding wp 3 using p2 by simp
      with mem2 show ?thesis using p2 res 3 rec2 by auto
    qed
    thus ?case unfolding wp_def by blast
  qed auto
  thus "?A \<Longrightarrow> ?B \<Longrightarrow> ?C \<Longrightarrow> ?D" by blast
qed

end
