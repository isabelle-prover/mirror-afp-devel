theory Memory
  imports Utils
begin

class vtype =
  fixes to_nat :: "'a \<Rightarrow> nat option"

section \<open>Memory\<close>

type_synonym location = nat

datatype 'v mdata =
  is_Value: Value (vt: 'v)
| is_Array: Array (ar: "location list")

definition case_memory where
  "case_memory m l vf af \<equiv>
    (case m$l of
      Some (mdata.Value v) \<Rightarrow> vf v
    | Some (mdata.Array xs) \<Rightarrow> af xs
    | None \<Rightarrow> None)"

lemma case_memory_cong[fundef_cong]:
  assumes "\<And>v. m$l = Some (mdata.Value v) \<Longrightarrow> vf1 v = vf2 v"
      and "\<And>xs. m$l = Some (mdata.Array xs) \<Longrightarrow> af1 xs = af2 xs"
    shows "case_memory m l vf1 af1 = case_memory m l vf2 af2"
  unfolding case_memory_def using assms by (simp split: option.split mdata.split) 

type_synonym 'v memory = "'v mdata list"

section \<open>Array Lookup\<close>

fun marray_lookup ::
    "'v::vtype memory \<Rightarrow> 'v list \<Rightarrow> location \<Rightarrow> (location \<times> location list \<times> nat) option"
  where
  "marray_lookup _ [] _  = None"
| "marray_lookup m [i] l =
    case_memory m l
      (K None)
      (\<lambda>xs. to_nat i \<bind> (\<lambda>i. Some (l, xs, i)))"
| "marray_lookup m (i # is) l =
    case_memory m l
      (K None)
      (\<lambda>xs. to_nat i \<bind> ($) xs \<bind> marray_lookup m is)"

lemma marray_lookup_obtain_single:
  assumes "marray_lookup m [i] l = Some a"
  obtains xs i''
  where "m $ l = Some (mdata.Array xs)"
    and "to_nat i = Some i''"
    and "a = (l, xs, i'')"
  using assms
  by (cases "to_nat i", auto simp add:case_memory_def split:option.split_asm mdata.split_asm)

lemma marray_lookup_obtain_multi:
  assumes "marray_lookup m (i # i' # is) l = Some a"
  obtains xs i'' l'
  where "m $ l = Some (mdata.Array xs)"
    and "to_nat i = Some i''"
    and "xs $ i'' = Some l'"
    and "marray_lookup m (i'#is) l' = Some a"
  using assms
  by (cases "to_nat i",
      auto simp add:case_memory_def nth_safe_def split: mdata.split_asm if_split_asm)

lemma marray_lookup_prefix:
  assumes "marray_lookup m xs l = Some x"
      and "prefix m m'"
    shows "marray_lookup m' xs l = Some x"
  using assms
proof (induction xs arbitrary: l)
  case Nil
  then show ?case by simp
next
  case (Cons i xs')
  then show ?case
  proof (cases xs')
    case Nil
    then show ?thesis using Cons
      apply (auto simp add:case_memory_def)
      apply (case_tac "m $ l", auto)
      apply (case_tac "a", auto)
      using nth_safe_prefix by fastforce 
  next
    case c: (Cons i' "is")
    then obtain xs i'' l'
    where "m $ l = Some (mdata.Array xs)"
      and "to_nat i = Some i''"
      and "xs $ i'' = Some l'"
      and *: "marray_lookup m (i'#is) l' = Some x"
      using marray_lookup_obtain_multi Cons(2) by blast
    moreover from * have "marray_lookup m' (i'#is) l' = Some x" using Cons(1,3) c by simp
    ultimately show ?thesis using Cons(3) c
      apply (auto simp add:case_memory_def)
      using nth_safe_prefix by fastforce 
  qed
qed

lemma marray_lookup_prefix_some:
  assumes "xs \<noteq> []"
    and "marray_lookup m (xs@ys) l = Some y"
  shows "\<exists>y. marray_lookup m xs l = Some y"
  using assms
proof (induction xs arbitrary: y l rule: list_nonempty_induct)
  case (single x)
  then show ?case
  apply (cases ys,auto simp add:case_memory_def)
  apply (cases "m$l",auto)
  apply (case_tac a,auto)
  apply (cases "to_nat x",auto)
  apply (cases "m$l",auto)
  apply (case_tac aa,auto)
  by (cases "to_nat x",auto)
next
  case (cons x xs)
  then obtain x' xs'
    where *: "marray_lookup m (x # x' # (xs' @ ys)) l = Some y"
      and **: "xs = x' # xs'"
    by (metis append_Cons neq_Nil_conv)
  then obtain ns i'' l'
    where 1: "m $ l = Some (mdata.Array ns)"
      and 2: "to_nat x = Some i''"
      and 3: "ns $ i'' = Some l'"
      and 4: "marray_lookup m (x' # xs' @ ys) l' = Some y"
    using marray_lookup_obtain_multi[OF *] by blast
  moreover from 1 2 3 4 obtain y
    where "marray_lookup m xs l' = Some y" using cons(2) **
    by fastforce 
  ultimately show ?case using **
    apply (auto simp add:case_memory_def)
    by (metis surj_pair)
qed

lemma marray_lookup_append:
  assumes "xs \<noteq> []"
      and "ys \<noteq> []"
    shows "marray_lookup m (xs @ ys) l
          = marray_lookup m xs l \<bind> (\<lambda>(l', ls, i). (ls $ i) \<bind> (\<lambda>i. marray_lookup m ys i))"
  using assms
proof (induction xs arbitrary: l)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  then obtain y ys' where *: "ys = y#ys'" by (meson list.exhaust)
  show ?case
  proof (cases xs)
    case Nil
    then show ?thesis using * by (auto simp add:case_memory_def nth_safe_def split: mdata.split)
  next
    case 1: Cons
    show ?thesis
    proof (cases "m $ l")
      case (Some md)
      then show ?thesis
      proof (cases md)
        case (Array ls)
        then have
          **: "marray_lookup m ((x # xs) @ ys) l = to_nat x \<bind> ($) ls \<bind> marray_lookup m (xs @ ys)"
          using 1 Some by (auto simp add:case_memory_def)
        show ?thesis
        proof (cases "to_nat x")
          case 2: (Some i)
          then show ?thesis
          proof (cases "ls $ i")
            case None
            then show ?thesis
              using Cons(1,3) 1 2 by (auto simp add:case_memory_def nth_safe_def split: mdata.split)
          next
            case 3: (Some l')
            then have
              "marray_lookup m (xs @ ys) l'
              = marray_lookup m xs l' \<bind> (\<lambda>a. case a of (l', ls, i) \<Rightarrow> ls $ i \<bind> marray_lookup m ys)"
              using Cons(1) * 1 by auto
            then show ?thesis using Some Array 1 2 3 by (auto simp add:case_memory_def)
          qed
        qed (auto simp add: 1 case_memory_def split:option.split mdata.split)
      qed (auto simp add: 1 case_memory_def)
    qed (auto simp add: 1 case_memory_def)
  qed
qed

section \<open>Memory Lookup\<close>

fun mlookup :: "'v::vtype memory \<Rightarrow> 'v list \<Rightarrow> location \<Rightarrow> location option" where
  "mlookup m [] l = Some l"
| "mlookup m xs l = marray_lookup m xs l \<bind> (\<lambda>(_, xs', i). xs' $ i)"

lemma mlookup_obtain_empty:
  assumes "mlookup m [] l = Some a"
  shows "a = l"
  using assms by simp

lemma mlookup_obtain_single:
  assumes "mlookup m [i] l = Some a"
  obtains xs i'
  where "m $ l = Some (mdata.Array xs)"
    and "to_nat i = Some i'"
    and "xs$i' = Some a"
  using assms
  by (cases "to_nat i", auto simp add:case_memory_def split:option.split_asm mdata.split_asm)

lemma mlookup_obtain_nempty1:
  assumes "mlookup m (x#xs) l = Some aa"
  obtains a xs' i i'
  where "marray_lookup m (x#xs) l = Some (a, xs', i)"
    and "xs' $ i = Some i'"
    and "aa = i'"
  using assms apply (auto)
  apply (cases "marray_lookup m (x # xs) l") by (auto)

lemma mlookup_obtain_nempty2:
  assumes "mlookup m (i # is) l = Some l'"
  obtains ls i' l''
  where "m$l = Some (mdata.Array ls)"
    and "to_nat i = Some i'"
    and "ls $ i' = Some l''"
    and "mlookup m is l'' = Some l'"
  using assms that
  apply (cases "is",auto simp add:case_memory_def)
   apply (cases "m$l",auto)
   apply (case_tac a,auto)
   apply (cases "to_nat i", auto)
  apply (cases "m$l",auto)
  apply (case_tac aa,auto)
  apply (cases "to_nat i", auto)
  by (case_tac "x2$aa",auto)

lemma mlookup_start_some:
  assumes "mlookup m (iv#is) l = Some l'"
  shows "\<exists>x. m$l = Some x"
  using assms
proof (cases rule:mlookup_obtain_nempty2)
  case (1 ls i' l'')
  then show ?thesis by blast
qed

lemma mlookup_same:
  assumes "xs \<noteq> []"
    and "m $ l1 = m $ l2"
  shows "mlookup m xs l1 = mlookup m xs l2"
  using assms
proof (induction xs arbitrary: l1 l2 rule: list_nonempty_induct)
  case (single x)
  then show ?case
    apply (cases "m$l2",auto simp add: case_memory_def)
    by (case_tac a,auto)
next
  case (cons x xs)
  then obtain x' xs' where xs_def: "xs=x'#xs'"
    by (meson list.exhaust)
  then show ?case
  proof (cases "m $ l1")
    case None
    then have "m $ l2 = None" using cons(3) by simp
    then show ?thesis using None xs_def
      by (simp add: case_memory_def)
  next
    case (Some a)
    then have "m $ l2 = Some a" using cons(3) by simp
    then show ?thesis using Some xs_def
    by (simp add: case_memory_def)
  qed
qed

lemma mlookup_prefix_mlookup:
  assumes "mlookup m xs0 l = Some x0"
     and "prefix m m'"
   shows "mlookup m' xs0 l = Some x0"
  using assms
proof (cases xs0)
  case Nil
  then show ?thesis using assms by auto
next
  case (Cons x xs)
  then obtain a xs' i i'
  where *: "marray_lookup m (x#xs) l = Some (a, xs', i)"
    and "xs' $ i = Some i'"
    and "x0 = i'"
  using mlookup_obtain_nempty1 assms(1) by metis
  moreover have "marray_lookup m' (x#xs) l = Some (a, xs', i)"
    using marray_lookup_prefix[OF * assms(2)] by blast
  ultimately show ?thesis using assms Cons by auto
qed

lemma mlookup_append:
  "mlookup m (xs @ ys) l = mlookup m xs l \<bind> mlookup m ys"
proof (cases xs)
  case 1: Nil
  then show ?thesis
  proof (cases ys)
    case Nil
    then show ?thesis using 1 by (auto simp add: nth_safe_def)
  next
    case 2: (Cons _ ys')
    then show ?thesis using 1 by (cases ys', auto simp add: nth_safe_def case_memory_def)
  qed
next
  case (Cons x xs')
  then show ?thesis
  proof (cases ys)
    case Nil
    then show ?thesis
    proof (cases xs')
      case 1: Nil
      then show ?thesis
        by (cases "to_nat x",
            auto simp add: Cons Nil case_memory_def nth_safe_def split: mdata.split)
    next
      case 1: (Cons x' xs')
      then show ?thesis
      proof (cases "to_nat x")
        case None
        then show ?thesis
          using Nil 1 Cons by (auto simp add: case_memory_def nth_safe_def split: mdata.split)
      next
        case (Some a)
        then show ?thesis using Nil 1 Cons
          apply (auto simp add:case_memory_def nth_safe_def
                      split:option.split mdata.split if_split_asm)
          apply (case_tac "marray_lookup m (x' # xs') (x2 ! a)")
          by (auto simp add:case_memory_def nth_safe_def
                   split:option.split mdata.split if_split_asm)
      qed
    qed
  next
    case 1: (Cons _ ys')
    then have
      lhs: "mlookup m (xs @ ys) l
            = marray_lookup m xs l
              \<bind> (\<lambda>(l', ls, i). ls $ i \<bind> marray_lookup m ys)
              \<bind> (\<lambda>(uu, xs', i). xs' $ i)"
      using marray_lookup_append[of xs ys m l] Cons by simp
    show ?thesis
    proof (cases "marray_lookup m xs l")
      case None
      then show ?thesis using Cons 1 lhs by simp
    next
      case (Some a)
      then show ?thesis
      proof (cases a)
        case (fields l' ls i)
        then show ?thesis 
        proof (cases "ls $ i")
          case None
          then show ?thesis using lhs Cons Some fields by auto
        next
          case 2: (Some a)
          then show ?thesis
          proof (cases "m $ a")
            case _: None
            then have "marray_lookup m ys a = None"
              using 1 by (cases ys', auto simp add: case_memory_def)
            then show ?thesis using lhs Cons Some fields 1 2 by auto
          next
            case _: (Some a)
            then show ?thesis using lhs Cons Some fields 1 2 by auto
          qed
        qed
      qed  
    qed
  qed
qed

section \<open>Memory Update\<close>

fun mupdate :: "'v::vtype list \<Rightarrow> location \<times> 'v mdata \<times> 'v memory \<Rightarrow> 'v memory option" where
  "mupdate xs (l, v, m) = mlookup m xs l \<bind> (\<lambda>l. list_update_safe m l v)"

lemma mvalue_update_obtain:
  assumes "mupdate xs (l,v,m) = Some x"
  obtains l'
  where "mlookup m xs l = Some l'"
    and "l' < length m"
    and "x = m[l':=v]"
  using assms by (cases "mlookup m xs l", auto simp add: list_update_safe_def split:if_split_asm)

lemma mvalue_update_length:
  assumes "mupdate is (ml, v, m) = Some m'"
    shows "length m' = length m"
  by (metis assms length_list_update mvalue_update_obtain)

section \<open>Memory Locations\<close>

fun locations :: "'v mdata list \<Rightarrow> 'v::vtype list \<Rightarrow> nat \<Rightarrow> nat fset option"  where
  "locations m [] l = Some ({||})"
| "locations m (i#is) l =
    case_memory m l
      (K None)
      (\<lambda>xs. to_nat i \<bind> ($) xs \<bind> (\<lambda>l'. locations m is l' \<bind> (\<lambda>ls. Some (finsert l ls))))"

lemma locations_obtain:
  assumes "locations m (i # is) l = Some L"
  obtains as i' l' L'
  where "m$l = Some (mdata.Array as)"
    and "to_nat i = Some i'"
    and "as $ i' = Some l'"
    and "locations m is l' = Some L'"
    and "L = (finsert l L')"
  using assms
  apply (cases "to_nat i", auto simp add:case_memory_def split:option.split_asm mdata.split_asm)
  by (case_tac "locations m is (x2a ! a)", auto simp add: nth_safe_def split: if_split_asm)

lemma locations_l_in_L:
  assumes "locations m (i#is') l = Some L"
    shows "l |\<in>| L"
proof-
  from assms obtain as i' l' L'
  where "m$l = Some (mdata.Array as)"
    and "to_nat i = Some i'"
    and "as $ i' = Some l'"
    and "locations m is' l' = Some L'"
    and "L = finsert l L'" using locations_obtain by blast
  then show ?thesis
    by (auto simp add: locations_obtain case_memory_def split:option.split_asm mdata.split_asm)
qed

lemma locations_same:
  assumes "locations m xs0 l = Some L"
     and "\<forall>l|\<in>|L. m' $ l = m $ l"
   shows "locations m' xs0 l = Some L"
  using assms
proof (induction xs0 arbitrary: l L)
  case Nil
  then show ?case
    by auto
next
  case (Cons i "is")
  then obtain as i' l' L'
  where "m$l = Some (mdata.Array as)"
    and "to_nat i = Some i'"
    and "as $ i' = Some l'"
    and *: "locations m is l' = Some L'"
    and **: "L = (finsert l L')"
    using locations_obtain by blast
  moreover from ** have "\<forall>l|\<in>|L'. m' $ l = m $ l"
    by (simp add: Cons.prems(2))
  then have "locations m' is l' = Some L'" using Cons(1)[OF *] by blast
  ultimately show ?case using Cons(3)
    by (auto simp add:case_memory_def)
qed


lemma locations_append_subset:
  assumes "locations m (xs @ xs') l = Some L"
  obtains L'
  where "locations m xs l = Some L'"
    and "L' |\<subseteq>| L"
  using assms
proof (induction xs arbitrary:L l)
  case Nil
  then show ?case using locations_l_in_L by auto
next
  case (Cons i "is")
  then obtain xs i' l' ls'
    where "m$l = Some (mdata.Array xs)"
      and "to_nat i = Some i'"
      and "xs $ i' = Some l'"
      and "locations m (is @ xs') l' = Some ls'"
      and "L = (finsert l ls')"
    using locations_obtain[of m i "is @xs'" l L] by (metis append_Cons)
  then show ?case using Cons(1)[of l' ls'] Cons(2) Cons(3)
    by (cases "locations m is l'") (auto simp add:case_memory_def)
qed

lemma locations_prefix_locations:
  assumes "locations m xs0 l = Some L"
     and "prefix m m'"
   shows "locations m' xs0 l = Some L"
  using assms
proof (induction xs0 arbitrary: l L)
  case Nil
  then show ?case
    by auto
next
  case (Cons i "is")
  then obtain as i' l' L'
  where "m$l = Some (mdata.Array as)"
    and "to_nat i = Some i'"
    and "as $ i' = Some l'"
    and *: "locations m is l' = Some L'"
    and "L = (finsert l L')"
    using locations_obtain by blast
  moreover have "locations m' is l' = Some L'" using Cons(1)[OF * Cons(3)] .
  ultimately show ?case using assms(2)
    apply (auto simp add:case_memory_def)
    using nth_safe_prefix by fastforce 
qed

lemma locations_subs_loc:
  assumes "locations m xs0 l = Some L"
    shows "fset L \<subseteq> loc m"
  using assms
proof (induction xs0 arbitrary: l L)
  case Nil
  then show ?case
    by auto
next
  case (Cons i "is")
  then obtain as i' l' L'
  where *: "m$l = Some (mdata.Array as)"
    and "to_nat i = Some i'"
    and "as $ i' = Some l'"
    and **: "locations m is l' = Some L'"
    and "L = (finsert l L')"
    using locations_obtain by blast
  moreover have "fset L' \<subseteq> loc m" using Cons(1)[OF **] .
  moreover from * have "l \<in> loc m" unfolding nth_safe_def apply (simp split:if_split_asm)
    by (simp add: loc_def)
  ultimately show ?case by blast
qed

section \<open>Locations and Array Lookup\<close>

lemma locations_marray_lookup_same:
  assumes "locations m1 is l = Some L"
      and "\<And>l. l |\<in>| L \<Longrightarrow> m1 $ l = m2 $ l"
    shows "marray_lookup m1 is l = marray_lookup m2 is l"
  using assms
proof (induction "is" arbitrary: l L)
  case Nil
  then show ?case by simp
next
  case (Cons i is')
  from Cons(3) Cons.prems(1) have 0: "m1$l = m2$l" using locations_l_in_L by blast
  from Cons(2) obtain xs i' l' ls'
    where 1: "m1$l = Some (mdata.Array xs)"
      and 2: "to_nat i = Some i'"
      and 3: "xs $ i' = Some l'"
      and 4: "locations m1 is' l' = Some ls'"
      and 5: "L = (finsert l ls')"
    using locations_obtain by blast
  from Cons(1)[OF 4] have 6: "marray_lookup m1 is' l' = marray_lookup m2 is' l'"
    by (simp add: Cons.prems(2) 5)
  show ?case
  proof (cases is')
    case Nil
    then show ?thesis using 0 by (simp add:case_memory_def)
  next
    case (Cons a list)
    then show ?thesis using 0 1 2 3 6 by (cases "m2$l", auto simp add:case_memory_def)
  qed
qed

lemma marray_lookup_in_locations:
  assumes "marray_lookup m is l = Some (l'', xs, i)"
      and "locations m is l = Some L"
    shows "l'' |\<in>| L"
  using assms
proof (induction "is" arbitrary:l L)
  case Nil
  then show ?case by simp
next
  case (Cons a xs')
  then show ?case
  proof (cases xs')
    case Nil
    then show ?thesis using Cons
      apply (auto simp add:case_memory_def split:option.split_asm mdata.split_asm)
      apply (cases "vtype_class.to_nat a",auto)
      by (cases "xs$i",auto)
  next
    case c: (Cons x xs'')
    then obtain l' xs''' x0' where b1: "marray_lookup m xs' l' = Some (l'', xs, i)"
      and b2: "m$l = Some (mdata.Array xs''')"
      and b3: "to_nat a = Some x0'"
      and b4: "xs''' $ x0' = Some l'"
      using Cons(2) c
      apply (auto simp add:case_memory_def split:option.split_asm mdata.split_asm)
      apply (cases "vtype_class.to_nat a", auto)
      apply (case_tac "x2a $ aa")
      by auto

    moreover from Cons(3) obtain L' where b2: "locations m xs' l' = Some L'" and "L' |\<subseteq>| L"
      apply (auto simp add:case_memory_def split:option.split_asm mdata.split_asm)
      apply (cases "vtype_class.to_nat a",simp)
      apply (case_tac "x2a $ aa", simp)
      apply (case_tac " locations m xs' aaa")
      using b2 b3 b4 by auto
    ultimately have "l'' |\<in>| L'" using Cons(1) Cons by blast
    then show ?thesis using \<open>L' |\<subseteq>| L\<close> by blast
  qed
qed

lemma marray_lookup_update_same:
  assumes "locations m xs l = Some L"
      and "\<not> (l' |\<in>| L)"
    shows "marray_lookup m xs l = marray_lookup (m[l':=v']) xs l"
proof -
  from assms(2) have "\<And>l. l |\<in>| L \<Longrightarrow> m $ l = m[l':=v'] $ l"
    by (metis length_list_update nth_list_update_neq nth_safe_def)
  then show ?thesis using locations_marray_lookup_same[OF assms(1)] by metis
qed

lemma marray_lookup_locations_some:
  assumes "marray_lookup m xs l = Some (l0, xs', i)"
      and "xs' $ i = Some i'"
  shows "\<exists>L. locations m xs l = Some L"
  using assms
proof (induction xs arbitrary:l)
  case Nil
  then show ?case by simp
next
  case (Cons i' "is")
  show ?case
  proof (cases "is")
    case Nil
    then show ?thesis using Cons(2,3) apply (auto simp add:case_memory_def)
      apply (case_tac "m$l",auto)
      apply (case_tac a,auto)
      by (case_tac "to_nat i'",auto)
  next
    case c: (Cons i'' is')
    then obtain xs i''' l'
    where "m $ l = Some (mdata.Array xs)"
      and "to_nat i' = Some i'''"
      and "xs $ i''' = Some l'"
      and *: "marray_lookup m (i'' # is') l' = Some (l0, xs', i)"
      using marray_lookup_obtain_multi[of m i' i'' is' l] Cons(2) Cons(3) by blast
    moreover from * obtain L where "locations m is l' = Some L" using Cons c by auto
    ultimately show ?thesis using Cons by (auto simp add:case_memory_def)
  qed
qed

lemma marray_lookup_in_locations2:
  assumes "xs \<noteq> []"
      and "ys \<noteq> []"
      and "marray_lookup m xs l = Some (l0, xs0, i0)"
      and "xs0 $ i0 = Some ll"
      and "locations m (xs@ys) l = Some L"
   shows "ll |\<in>| L"
  using assms
proof (induction "xs" arbitrary: m l L rule: list_nonempty_induct)
  case (single i)
  then obtain xs i''
    where "m $ l = Some (mdata.Array xs)"
      and "to_nat i = Some i''"
      and "(l0, xs0, i0) = (l, xs, i'')"
    using marray_lookup_obtain_single by blast
  then show ?case using single
    apply (case_tac "locations m ys ll", auto simp add:case_memory_def)
    by (metis list.exhaust_sel locations_l_in_L)
next
  case (cons i "is")
  then obtain i' is' where is_def: "is = i' # is'" 
    by (meson list.exhaust)
  with cons(4) have *: "marray_lookup m (i # i' # is') l = Some (l0, xs0, i0)" by simp
  obtain xs i'' l'
  where "m $ l = Some (mdata.Array xs)"
    and "to_nat i = Some i''"
    and "xs $ i'' = Some l'"
    and l4: "marray_lookup m is l' = Some (l0, xs0, i0)"
    using marray_lookup_obtain_multi[OF *] is_def by auto
  moreover from cons(6) have *: "locations m (i # (is @ ys)) l = Some L" by simp
  ultimately obtain L' where "locations m (is @ ys) l' = Some L'" 
    and "L = (finsert l L')"
    using locations_obtain[OF *] by force
  with cons(2)[OF cons(3) l4 cons(5)] show ?case by simp
qed

section \<open>Locations and Lookup\<close>

lemma mlookup_update_val:
  assumes "mlookup m xs l = Some l'"
      and "locations m xs l = Some L"
      and "\<not> (l'' |\<in>| L)"
    shows "mlookup (m[l'':=v]) xs l = Some l'"
  using assms
proof (cases xs)
  case Nil
  then have "l = l'"
    using mlookup_obtain_empty assms(1) by blast
  then have "mlookup (m[l'':=v]) [] l = Some l'"
    by (cases "m[l':=v]$l", auto simp add: nth_safe_def split:if_split_asm)
  then show ?thesis using Nil(1) by simp
next
  case (Cons x xs'')
  then obtain a xs' i i'
    where "marray_lookup m (x # xs'') l = Some (a, xs', i)"
      and "xs' $ i = Some i'"
      and "l' = i'"
    using mlookup_obtain_nempty1[of m x xs'' l "l'"] assms(1) by metis
  moreover have "marray_lookup m xs l = marray_lookup (m[l'':=v]) xs l"
    using marray_lookup_update_same[OF assms(2) assms(3)] by simp
  ultimately show ?thesis using Cons(1) assms
    by (cases "marray_lookup (m[i' := v]) (x # xs'') l")
       (auto simp add:nth_safe_def split:if_split_asm)
qed

lemma mlookup_locations_some:
  assumes "mlookup m xs0 l = Some l'"
  shows "\<exists>L. locations m xs0 l = Some L"
  using assms
proof (cases xs0)
  case Nil
  then show ?thesis by simp
next
  case (Cons x xs)

  then obtain a xs' i i'
  where "marray_lookup m (x#xs) l = Some (a, xs', i)"
    and "xs' $ i = Some i'"
    and "l' = i'" using mlookup_obtain_nempty1 assms(1)
    by metis

  then obtain L where "locations m (x#xs) l = Some L" using marray_lookup_locations_some by blast
  then show ?thesis using Cons by blast
qed

lemma mlookup_update_same_nempty:
  assumes "mlookup m (x#xs) l1 = Some l1'"
      and "locations m (x#xs) l1 = Some L"
      and "\<not> (l2 |\<in>| L)"
    shows "mlookup (m[l2:=v']) (x#xs) l1 = mlookup m (x#xs) l1"
  using mlookup_update_val[OF assms(1,2)]
proof -
  from assms(1) obtain a xs' i i'
      where "marray_lookup m (x # xs) l1 = Some (a, xs', i)"
        and "xs' $ i = Some i'"
        and "l1' = i'"
      using mlookup_obtain_nempty1[of m x xs l1 "l1'"] assms(1) by metis
  moreover have "marray_lookup m (x#xs) l1 = marray_lookup (m[l2:=v']) (x#xs) l1"
    using marray_lookup_update_same[OF assms(2) assms(3)] by simp
  ultimately show ?thesis using Cons(1)
      by (auto simp add:nth_safe_def split:if_split_asm)
qed

lemma mlookup_in_locations:
  assumes "ys \<noteq> []"
     and "mlookup m xs l = Some l'"
     and "locations m (xs@ys) l = Some L"
   shows "l' |\<in>| L"
  using assms
proof (cases xs)
  case Nil
  then show ?thesis using assms
    by (metis list.exhaust locations_l_in_L mlookup_obtain_empty self_append_conv2)
next
  case (Cons a list)
  then show ?thesis
    by (metis assms(1,2,3) list.distinct(1) marray_lookup_in_locations2 mlookup_obtain_nempty1)
qed

lemma mlookup_access_same:
  assumes "locations m1 xs l = Some L"
      and "mlookup m1 xs l = Some l'"
      and "\<And>l. l |\<in>| L \<Longrightarrow> m1 $ l = m2 $ l"
      and "m1 $ l' = m2 $ l'"
    shows "mlookup m2 xs l \<bind> ($) m2 = m1 $ l'"
proof (cases xs)
  case Nil
  then show ?thesis using assms by simp
next
  case (Cons x' xs')
  then have "mlookup m2 xs l = Some l'"
    using locations_marray_lookup_same[OF assms(1,3)] assms(2) by simp
  then show ?thesis using assms(4) by auto
qed

lemma mlookup_same_locations:
  assumes "mlookup m1 xs l = Some l'"
      and "locations m1 xs l = Some L"
      and "\<forall>l |\<in>| L. m1 $ l = m2 $ l"
    shows "mlookup m2 xs l = Some l'"
  using assms
proof (cases xs)
  case Nil
  then show ?thesis
    using assms(1) by auto
next
  case (Cons x xs')
  then obtain a xs'' i i'
  where "marray_lookup m1 (x#xs') l = Some (a, xs'', i)"
    and "xs'' $ i = Some i'"
    and "l' = i'"
    using mlookup_obtain_nempty1 assms(1) by blast
  then have "marray_lookup m1 xs l = marray_lookup m2 xs l"
    using locations_marray_lookup_same[OF assms(2), of m2] assms(3) by blast
  then show ?thesis using assms(1) local.Cons by fastforce 
qed

lemma mlookup_append_same:
  assumes "ys \<noteq> []"
      and "mlookup m xs1 l1 = Some l1'"
      and "m $ l1' = Some l1''"
      and "mlookup m xs2 l2 \<bind> ($) m = Some l1''"
    shows "mlookup m (xs1 @ ys) l1 = mlookup m (xs2 @ ys) l2" (is "?LHS=?RHS")
proof -
  from assms(4) obtain l2' where ls'_def: "mlookup m xs2 l2 = Some l2'" and l1''_def: "m $ l2' = Some l1''"
    by (meson bind_eq_Some_conv)
  have "?LHS = mlookup m xs1 l1 \<bind> mlookup m ys" using mlookup_append by blast
  also have "\<dots> = mlookup m ys l1'" using assms by simp
  also have "\<dots> = mlookup m ys l2'" using mlookup_same[OF assms(1)] assms(3) l1''_def by auto
  also have "\<dots> = mlookup m xs2 l2 \<bind> mlookup m ys" using ls'_def by simp
  also have "\<dots> = ?RHS" using mlookup_append by metis
  finally show ?thesis .
qed

lemma locations_union_nth:
  assumes "xs = x#xs'"
      and "m0 $ l0 = m1 $ l1"
      and "mlookup m0 [x] l0 = Some l"
      and "locations m0 xs' l = Some L"
      and "\<forall>l |\<in>| L. m0$l=m1$l"
    shows "locations m1 xs l1 = Some (finsert l1 L)"
proof -
  from assms(1) have "xs \<noteq> []" by simp
  then show ?thesis using assms
  proof (induction xs arbitrary: l0 l1 L l x xs' rule: list_nonempty_induct)
    case (single x)
    then show ?case apply (simp add:case_memory_def split:option.split_asm mdata.split_asm)
      by (case_tac "vtype_class.to_nat x", auto)
  next
    case (cons i "is")
    moreover obtain as i'
      where ls_def: "m0 $ l0 = Some (Array as)"
        and i'_def: "vtype_class.to_nat x = Some i'" and l_def: "as $ i' = Some l"
      using mlookup_obtain_single[OF cons(5)] by blast    
    moreover from ls_def have as_def: "m1$l1 = Some (Array as)" using cons by argo
    moreover obtain LL where LL_def: "locations m1 is l = Some LL"
      by (metis cons.prems(1,4,5) list.inject locations_same)
    ultimately have "locations m1 (i # is) l1 = Some (finsert l1 LL)" by (auto simp add: case_memory_def)
    show ?case
    proof (cases xs')
      case Nil
      then show ?thesis using cons by simp
    next
      case (Cons x' xs'')
      moreover have "m0 $ l = m1 $ l"
        using calculation cons.prems(4,5) locations_l_in_L by blast
      moreover obtain l2 where "mlookup m0 [x'] l = Some l2" using cons(6) Cons  apply (auto simp add:case_memory_def split:option.split_asm mdata.split_asm)
        apply (case_tac "vtype_class.to_nat x'",auto)
        by (case_tac " x2a $ a",auto)
      moreover obtain L2 where "locations m0 xs'' l2 = Some L2" and L2_def: "L = (finsert l L2)" using cons(6) Cons apply (auto simp add:case_memory_def split:option.split_asm mdata.split_asm)
        apply (case_tac "vtype_class.to_nat x'",auto)
        apply (case_tac " x2a $ a",auto)
        apply (case_tac "locations m0 xs'' aa",auto)
        by (metis calculation(3) mdata.inject(2) mlookup_obtain_single option.sel)
      moreover have "\<forall>l|\<in>|L2. m0 $ l = m1 $ l"
        by (simp add: L2_def cons.prems(5))
      ultimately have "locations m1 is l = Some (finsert l L2)" using cons(2)[of x' xs'' l l l2 L2]
        using cons.prems(1) by blast 
      then show ?thesis using as_def LL_def i'_def cons(3) l_def L2_def by (simp add:case_memory_def)
    qed
  qed
qed

lemma locations_union_mlookup_nth:
  assumes "ys = y#ys'"
      and "mlookup m0 xs l = Some l'"
      and "m0 $ l'' = m1 $ l'"
      and "mlookup m0 [y] l'' = Some ll"
      and "locations m0 xs l = Some L0"
      and "\<forall>l |\<in>| L0. m0$l=m1$l"
      and "locations m0 ys' ll = Some L1"
      and "\<forall>l |\<in>| L1. m0$l=m1$l"
    shows "locations m1 (xs @ ys) l = Some (finsert l' L0 |\<union>| L1)"
  using assms
proof (induction xs arbitrary: l l' L0)
  case Nil
  then have "locations m1 ys l = Some (finsert l L1)"
    using locations_union_nth[of ys y ys' m0 l'' m1 l ll L1] by auto
  moreover from Nil have "L0 = {||}" by simp
  ultimately show ?case using Nil.prems(2) by force
next
  case (Cons i "is")
  obtain ls i' l''
    where ls_def: "m0 $ l = Some (Array ls)"
      and i'_def: "vtype_class.to_nat i = Some i'"
      and l''_def: "ls $ i' = Some l''"
      and l'_def: "mlookup m0 is l'' = Some l'"
    using mlookup_obtain_nempty2[OF Cons(3)] by blast
  moreover from ls_def i'_def l''_def obtain L'
  where L'_def: "locations m0 is l'' = Some L'"
    and L0_def: "L0 = (finsert l L')"
    using locations_obtain[OF Cons(6)] by force
  moreover have "locations m1 (is @ ys) l'' = Some (finsert l' L' |\<union>| L1)"
    using Cons(1)[OF Cons(2) l'_def Cons(4,5) L'_def _ Cons(8,9)] Cons(7) L0_def by auto
  ultimately show ?case using Cons(7) by (auto simp add:case_memory_def split:option.split mdata.split)
qed

lemma locations_union_mlookup:
  assumes "mlookup m xs l = Some l'"
      and "locations m xs l = Some L0"
      and "locations m ys l' = Some L1"
    shows "locations m (xs @ ys) l = Some (L0 |\<union>| L1)"
  using assms
proof (induction xs arbitrary: l l' L0)
  case Nil
  then show ?case
    by simp
next
  case (Cons i "is")
  obtain ls i' l''
    where ls_def: "m $ l = Some (Array ls)"
      and i'_def: "vtype_class.to_nat i = Some i'"
      and l''_def: "ls $ i' = Some l''"
      and l'_def: "mlookup m is l'' = Some l'"
    using mlookup_obtain_nempty2[OF Cons(2)] by blast
  moreover from ls_def i'_def l''_def obtain L'
  where L'_def: "locations m is l'' = Some L'"
    and "L0 = (finsert l L')"
    using locations_obtain[OF Cons(3)] by force
  moreover have "locations m (is @ ys) l'' = Some (L' |\<union>| L1)"
    using Cons(1)[OF l'_def L'_def Cons(4)] by simp
  ultimately show ?case by (auto simp add:case_memory_def)
qed

lemma mlookup_locations_subs:
  assumes "mlookup m xs l = Some l'"
      and "locations m (xs @ ys) l = Some L0"
      and "locations m ys l' = Some L1"
    shows "L1 |\<subseteq>| L0"
proof -
  from assms(1) obtain L where "locations m xs l = Some L" using locations_append_subset[OF assms(2)] by metis
  then show ?thesis using locations_union_mlookup[OF assms(1) _ assms(3)] assms(2) by simp
qed

proposition is_none_mlookup_locations:
  assumes "\<not> Option.is_none (mlookup m xs l)"
    shows "\<not> Option.is_none (locations m xs l)"
  using assms
proof (induction xs arbitrary:l)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  then obtain aa where a_def: "mlookup m (x # xs) l = Some aa"
    by (metis Option.is_none_def option.exhaust)
  then obtain a xs' i i'
  where a1: "marray_lookup m (x#xs) l = Some (a, xs', i)"
    and a2: "xs' $ i = Some i'"
    and a4: "aa = i'"
    using mlookup_obtain_nempty1 by metis
  then show ?case
  proof (cases xs)
    case Nil
    then show ?thesis using a1 a2 a4 Cons
      apply (auto simp add:case_memory_def split:option.split_asm mdata.split_asm)
      apply (cases "vtype_class.to_nat x") by auto
  next
    case c: (Cons a' list)
    then obtain l' xs'' x0' where b1: "marray_lookup m xs l' = Some (a, xs', i)"
      and "m$l = Some (mdata.Array xs'')"
      and "to_nat x = Some x0'"
      and "xs'' $ x0' = Some l'"
      using a1 a4 Cons(2)
      apply (auto simp add:case_memory_def split:option.split_asm mdata.split_asm)
      apply (cases "vtype_class.to_nat x") apply auto
      apply (case_tac "x2a $ ab") by auto
    moreover have "\<not> Option.is_none (locations m xs l')" using a1 c Cons.IH Cons.prems b1 by auto
    moreover from a1 c obtain
      xs'' where "m$l = Some (mdata.Array xs'')" using marray_lookup_obtain_multi by blast
    ultimately show ?thesis
      apply (simp add:case_memory_def)
    using Option.is_none_def by fastforce
  qed
qed

lemma locations_app_mlookup_exists:
  assumes "locations m (xs @ ys) l0 = Some L"
      and "mlookup m xs l0 = Some l1"
    shows "\<exists>L' L''. locations m xs l0 = Some L' \<and> locations m ys l1 = Some L'' \<and> L = L' |\<union>| L''"
  using assms
proof (induction xs arbitrary:l0 L)
  case Nil
  then show ?case by simp
next
  case (Cons x xs')
  then obtain ls i' l'
  where ls_def: "m$l0 = Some (mdata.Array ls)"
    and i'_def: "to_nat x = Some i'"
    and l'_def: "ls $ i' = Some l'"
    and l1_def: "mlookup m xs' l' = Some l1"
    using mlookup_obtain_nempty2[OF Cons(3)] by blast
  moreover from ls_def i'_def l'_def obtain L'
  where L'_def: "locations m (xs' @ ys) l' = Some L'"
    and "L = (finsert l0 L')" 
    using locations_obtain[of m x "xs' @ ys" l0] using Cons(2) by force
  moreover from Cons(1)[OF L'_def l1_def]
  obtain L'' L'''
    where "locations m xs' l' = Some L''"
      and "locations m ys l1 = Some L'''"
      and "L' = L'' |\<union>| L'''" by auto
  ultimately show ?case by (auto simp add: case_memory_def)
qed

lemma locations_cons_mlookup_exists:
  assumes "locations m0 (z#zs) l0 = Some L"
    and "mlookup m0 [z] l0 = Some l1"
  shows "\<exists>L'. locations m0 zs l1 = Some L' \<and> L' |\<subseteq>| L"
  using assms apply (auto simp add: case_memory_def split:option.split_asm mdata.split_asm)
  apply (cases "vtype_class.to_nat z", auto)
  by (cases "locations m0 zs l1", auto)

lemma mlookup_mlookup_mlookup:
  assumes "mlookup m0 ys l1 = Some l1'"
      and "m1 $ l1' = m0 $ l0'"
      and "zs \<noteq> []"
      and "\<forall>l|\<in>|the (locations m0 zs l0'). m0 $ l = m1 $ l"
      and "\<forall>l|\<in>|the (locations m0 ys l1). m0 $ l = m1 $ l"
      and "mlookup m0 zs l0' = Some l2"
    shows "mlookup m1 (ys @ zs) l1 = Some l2"
  using assms
proof -
  from assms have "mlookup m1 ys l1 = Some l1'" using mlookup_same_locations[OF assms(1)]
    by (metis mlookup_locations_some option.sel)
  moreover from assms  have "mlookup m1 zs l0' = Some l2" using mlookup_same_locations[OF assms(6)]
    by (metis mlookup_locations_some option.sel)
  moreover have "m1 $ l1' = m1 $ l0'"
    by (metis assms(2,3,4,6) locations.elims locations_l_in_L mlookup_locations_some option.sel)
  ultimately show ?thesis
    by (metis assms(3) bind.bind_lunit mlookup_append mlookup_same)
qed

locale data =
  fixes Value :: "'v::vtype \<Rightarrow> 'd"
    and Array :: "'d list \<Rightarrow> 'd"
begin

section \<open>Memory Locations\<close>

function range_safe :: "location fset \<Rightarrow> 'v memory \<Rightarrow> location \<Rightarrow> (location fset) option" where
  "range_safe s m l = 
   (if l |\<in>| s then None else
      case_memory m l
        (\<lambda>v. Some {|l|})
        (\<lambda>xs. fold
          (\<lambda>x y. y \<bind> (\<lambda>y'. (range_safe (finsert l s) m x) \<bind> (\<lambda>l. Some (l |\<union>| y'))))
          xs
          (Some {|l|})))"
by pat_completeness auto
termination
  apply (relation "measure (\<lambda>(s,m,_). card ({0..length m} - fset s))")
  using card_less_card by simp_all

lemma range_safe_obtains:
  assumes "range_safe s m l = Some x"
    obtains
    (1) v where "l |\<notin>| s"
    and "m $ l = Some (mdata.Value v)"
    and "x = {|l|}"
  | (2) xs where "l |\<notin>| s"
    and "m $ l = Some (mdata.Array xs)"
    and "fold
          (\<lambda>x y. y \<bind> (\<lambda>y'. (range_safe (finsert l s) m x) \<bind> (\<lambda>l. Some (l |\<union>| y'))))
          xs
          (Some {|l|})
        = Some x"
  using assms
  by (cases "m$l", auto split:if_split_asm mdata.split_asm simp add: case_memory_def)

lemma range_safe_subs:
  assumes "range_safe s m l = Some X"
  shows "l |\<in>| X"
  using assms
proof (cases rule: range_safe_obtains)
  case (1 v)
  then show ?thesis by simp
next
  case (2 xs)
  then show ?thesis using fold_some by force
qed

lemma range_safe_subs2:
  assumes "range_safe s m l = Some X"
    shows "fset X \<subseteq> loc m"
  using assms
proof (induction l arbitrary: X rule:range_safe.induct[where ?a0.0=s])
  case (1 s m l)
  from 1(2) show ?case
  proof (cases rule:range_safe_obtains)
    case 2: (1 v)
    show ?thesis
    proof
      fix x assume "x |\<in>| X"
      then have "l = x" using 2 by simp
      moreover have "l \<in> loc m" using 2(2)
        unfolding loc_def nth_safe_def by (simp split:if_split_asm)
      ultimately show "x \<in> loc m" by simp
    qed
  next
    case (2 xs)
    moreover have "l \<in> loc m"
      by (simp add: 2(2) loc_def nth_safe_length)
    moreover have "\<forall>x \<in> set xs. \<forall>L. range_safe (finsert l s) m x = Some L \<longrightarrow> fset L \<subseteq> loc m"
      using 1(1)[OF 2(1,2)] by simp
    ultimately show ?thesis using fold_subs[of _ "range_safe (finsert l s) m"] by blast
  qed
qed

lemma range_safe_obtains_subset:
  assumes "range_safe s m l = Some L"
      and "m $ l = Some (mdata.Array xs)"
      and "l' \<in> set xs"
    obtains L' where "range_safe (finsert l s) m l' = Some L'" and "L' |\<subseteq>| L"
  using assms
proof -
  from assms(1) have "l |\<notin>| s" by auto
  with assms(1,2) have "fold (\<lambda>x y. y \<bind> (\<lambda>y'. range_safe (finsert l s) m x \<bind> (\<lambda>l. Some (l |\<union>| y')))) xs (Some {|l|}) =
    Some L" by (simp add:case_memory_def)
  then show ?thesis by (metis assms(3) fold_some_subs that)
qed

lemma range_safe_nin_same:
  assumes "range_safe s m l = Some L"
      and "\<forall>l |\<in>| s' - s. l |\<notin>| L"
    shows "range_safe s' m l = Some L"
  using assms
proof (induction l arbitrary: L s' rule:range_safe.induct[where ?a0.0=s])
  case (1 s m l)
  from 1(2) show ?case
  proof (cases rule:range_safe_obtains)
    case _: (1 v)
    then show ?thesis using 1(3) by (auto simp add:case_memory_def)
  next
    case (2 xs)
    moreover from 2(1) 1(3) have "l |\<notin>| s'" using "1.prems"(1) range_safe_subs by blast
    moreover have
      "fold (\<lambda>x y. y \<bind> (\<lambda>y'. range_safe (finsert l s) m x \<bind> (\<lambda>l. Some (l |\<union>| y')))) xs (Some {|l|})
      = fold (\<lambda>x y. y \<bind> (\<lambda>y'. range_safe (finsert l s') m x \<bind> (\<lambda>l. Some (l |\<union>| y')))) xs (Some {|l|})"
    proof (rule fold_same)
      show "\<forall>x\<in>set xs. range_safe (finsert l s) m x = range_safe (finsert l s') m x"
      proof
        fix x assume "x \<in> set xs"
        moreover from `x \<in> set xs` obtain y
          where "range_safe (finsert l s) m x = Some y"
            and "y |\<subseteq>| L"
          using fold_some_subs[OF 2(3)] by blast
        moreover from 1(3) have "\<forall>l|\<in>|finsert l s' |-| finsert l s. l |\<notin>| y"
          using `y |\<subseteq>| L` by blast
        ultimately show "range_safe (finsert l s) m x = range_safe (finsert l s') m x"
          using 1(1)[OF 2(1,2), of x _ _ y "finsert l s'"] by simp
      qed
    qed
    ultimately show ?thesis by (auto simp add:case_memory_def)
  qed
qed

lemma range_safe_same:
  assumes "range_safe s m l = Some L"
      and "\<forall>l'|\<in>|L. m' $ l' = m $ l'"
    shows "range_safe s m' l = Some L"
  using assms
proof (induction l arbitrary: L rule:range_safe.induct)
  case (1 s m' l)
  from 1(2) show ?case
  proof (cases rule: range_safe_obtains)
    case _: (1 v)
    then show ?thesis using 1 by (auto simp add: case_memory_def)
  next
    case (2 xs)
    moreover have "l |\<in>| L" by (meson "1.prems"(1) range_safe_subs)
    ultimately have "m' $ l = Some (mdata.Array xs)" using 1 by auto
    moreover
      have
        "fold (\<lambda>x y. y \<bind> (\<lambda>y'. range_safe (finsert l s) m x \<bind> (\<lambda>l. Some (l |\<union>| y')))) xs (Some {|l|})
        = fold (\<lambda>x y. y \<bind> (\<lambda>y'. range_safe (finsert l s) m' x \<bind> (\<lambda>l. Some (l |\<union>| y')))) xs (Some {|l|})"
    proof (rule fold_same)
      show "\<forall>x\<in>set xs. range_safe (finsert l s) m x = range_safe (finsert l s) m' x"
      proof
        fix x assume "x \<in> set xs"
        moreover from `x \<in> set xs` obtain y
          where "range_safe (finsert l s) m x = Some y" and "y |\<subseteq>| L"
          using fold_some_subs[OF 2(3)] by blast
        moreover from `y |\<subseteq>| L` have "\<forall>l'|\<in>|y. m' $ l' = m $ l'" using 1(3) by blast
        ultimately show "range_safe (finsert l s) m x = range_safe (finsert l s) m' x"
          using 1(1)[OF 2(1) `m' $ l = Some (mdata.Array xs)`] by simp
      qed
    qed
    ultimately show ?thesis using 2 by (auto simp add:case_memory_def)
  qed
qed

lemma range_safe_same4:
  assumes "range_safe s m l = Some L"
      and "\<forall>l'|\<in>|L. (\<exists>xs. m' $ l' = Some (mdata.Array xs) \<and> m $ l' = Some (mdata.Array xs)) \<or> (\<exists>xs. m' $ l' = Some (mdata.Value xs))"
    shows "\<exists>L'. range_safe s m' l = Some L'"
  using assms
proof (induction l arbitrary: L rule:range_safe.induct)
  case (1 s m' l)
  from 1(2) show ?case
  proof (cases rule: range_safe_obtains)
    case _: (1 v)
    then show ?thesis using 1 by (auto simp add: case_memory_def)
  next
    case (2 xs)
    moreover have "l |\<in>| L" by (meson "1.prems"(1) range_safe_subs)
    ultimately consider "m' $ l = Some (mdata.Array xs)" | "\<exists>xs. m' $ l = Some (mdata.Value xs)" using 1 by auto
    then show ?thesis
    proof (cases)
      case a: 1
      moreover have "fold (\<lambda>x y. y \<bind> (\<lambda>y'. range_safe (finsert l s) m' x \<bind> (\<lambda>l. Some (l |\<union>| y')))) xs (Some {|l|}) \<noteq> None"
      proof (rule fold_f_set_some)
        show "\<forall>a\<in>set xs. range_safe (finsert l s) m' a \<noteq> None"
        proof
          fix a assume "a\<in>set xs"
          moreover from 1(2) obtain L' where "range_safe (finsert l s) m a = Some L'" and "L' |\<subseteq>| L"
            by (meson "2"(2) calculation range_safe_obtains_subset)
          moreover from 1(3) have "\<forall>l'|\<in>|L'. (\<exists>xs. m' $ l' = Some (mdata.Array xs) \<and> m $ l' = Some (mdata.Array xs)) \<or> (\<exists>xs. m' $ l' = Some (mdata.Value xs))"
            using calculation(3) by auto
          ultimately show "range_safe (finsert l s) m' a \<noteq> None" using 1(1)[OF 2(1),of xs a _ _ L'] a by blast
        qed
      qed
      ultimately show ?thesis using 1 by (auto simp add:case_memory_def)
    next
      case _: 2
      then show ?thesis using 1 2 \<open>l |\<in>| L\<close> by (simp add:case_memory_def nth_safe_def split: if_split_asm)
    qed
  qed
qed

lemma range_safe_subs3:
  assumes "range_safe s m l = Some L"
      and "\<forall>l'|\<in>|L. (\<exists>xs. m' $ l' = Some (mdata.Array xs) \<and> m $ l' = Some (mdata.Array xs)) \<or> (\<exists>xs. m' $ l' = Some (mdata.Value xs))"
    shows "\<exists>L'. range_safe s m' l = Some L' \<and> L' |\<subseteq>| L"
  using assms
proof (induction l arbitrary: L rule:range_safe.induct)
  case (1 s m' l)
  from 1(2) show ?case
  proof (cases rule: range_safe_obtains)
    case _: (1 v)
    then show ?thesis using 1 by (auto simp add: case_memory_def)
  next
    case (2 xs)
    moreover have "l |\<in>| L" by (meson "1.prems"(1) range_safe_subs)
    ultimately consider "m' $ l = Some (mdata.Array xs)" | "\<exists>xs. m' $ l = Some (mdata.Value xs)" using 1 by auto
    then show ?thesis
    proof (cases)
      case a: 1
      moreover from range_safe_same4[OF 1(2,3)] obtain L' where "range_safe s m' l = Some L'" by blast
      then have
          "fold (\<lambda>x y. y \<bind> (\<lambda>y'. range_safe (finsert l s) m' x \<bind> (\<lambda>l. Some (l |\<union>| y')))) xs (Some {|l|}) = Some L'"
        using 1 a 2 by (auto simp add:case_memory_def)
      then obtain L' where *: "fold (\<lambda>x y. y \<bind> (\<lambda>y'. range_safe (finsert l s) m' x \<bind> (\<lambda>l. Some (l |\<union>| y')))) xs (Some {|l|}) = Some (L')" by auto
      moreover have "fset L' \<subseteq> fset L"
      proof (rule fold_subs[OF _ *])
        from \<open>l |\<in>| L\<close> show "fset {|l|} \<subseteq> fset L" by auto
      next
        show "\<forall>x\<in>set xs. \<forall>L'. range_safe (finsert l s) m' x = Some L' \<longrightarrow> fset L' \<subseteq> fset L"
        proof (rule,rule,rule)
          fix x L' assume "x \<in> set xs"
          and "range_safe (finsert l s) m' x = Some L'"
          moreover obtain L'' where "range_safe (finsert l s) m x = Some L''" and "L'' |\<subseteq>| L"
            using "1.prems"(1) "2"(2) calculation(1) range_safe_obtains_subset by blast
          moreover have "\<forall>l'|\<in>|L''. (\<exists>xs. m' $ l' = Some (mdata.Array xs) \<and> m $ l' = Some (mdata.Array xs)) \<or> (\<exists>xs. m' $ l' = Some (mdata.Value xs))" using 1(3) \<open>L'' |\<subseteq>| L\<close> by auto
          ultimately show "fset L' \<subseteq> fset L" using 1(1)[OF 2(1) a, of x _ _ L''] by fastforce
        qed
      qed
      ultimately show ?thesis using 1 a by (auto simp add:case_memory_def)
    next
      case _: 2
      then show ?thesis using 1 2 \<open>l |\<in>| L\<close> by (simp add:case_memory_def nth_safe_def split: if_split_asm)
  qed
qed
qed

lemma range_safe_subset_same:
  assumes "range_safe s m l = Some x"
    and "s' |\<subseteq>| s"
  shows "range_safe s' m l = Some x"
  using assms
proof (induction arbitrary: s x rule:range_safe.induct)
  case (1 s' m l)
  from 1(2) show ?case
  proof (cases rule: range_safe_obtains)
    case _: (1 v)
    then show ?thesis using 1 by (auto simp add: case_memory_def)
  next
    case (2 xs)
    moreover
      have
        "fold (\<lambda>x y. y \<bind> (\<lambda>y'. range_safe (finsert l s) m x \<bind> (\<lambda>l. Some (l |\<union>| y')))) xs (Some {|l|})
        = fold (\<lambda>x y. y \<bind> (\<lambda>y'. range_safe (finsert l s') m x \<bind> (\<lambda>l. Some (l |\<union>| y')))) xs (Some {|l|})"
    proof (rule fold_same)
      show "\<forall>x\<in>set xs. range_safe (finsert l s) m x = range_safe (finsert l s') m x"
      proof
        fix x assume "x \<in> set xs"
        moreover from `x \<in> set xs` obtain y
          where " range_safe (finsert l s) m x = Some y" using fold_some_subs[OF 2(3)] by blast
        ultimately show "range_safe (finsert l s) m x = range_safe (finsert l s') m x" using 1 2
          by (metis fin_mono finsert_mono)
      qed
    qed
    ultimately show ?thesis using 1(3) by (auto simp add:case_memory_def)
  qed
qed

lemma range_safe_in_subs:
  assumes "range_safe s m l = Some L"
      and "l' |\<in>| L"
    shows "\<exists>L'. range_safe s m l' = Some L' \<and> L' |\<subseteq>| L"
  using assms
proof (induction l arbitrary: L rule:range_safe.induct[where ?a0.0=s])
  case (1 s m l)
  from 1(2) show ?case
  proof (cases rule:range_safe_obtains)
    case _: (1 v)
    then show ?thesis using 1(3) apply auto
      using "1.prems"(1) by auto
    next
    case (2 xs)
    show ?thesis
    proof (cases "l = l'")
      case True
      then have "range_safe s m l' = Some L"
        using 2 1 by (auto simp add:case_memory_def)
      then show ?thesis using fold_some[OF 2(3)] by simp 
    next
      case False
      then obtain x L'' where "x \<in> set xs" and "range_safe (finsert l s) m x = Some L''" and "l' |\<in>| L''" and "L'' |\<subseteq>| L" using 1(3) fold_some_ex[OF 2(3)] fold_some_subs[OF 2(3)] by fastforce
      then have "\<exists>L'. range_safe s m l' = Some L' \<and> L' |\<subseteq>| L''" using 1(1)[OF 2(1,2)]
        by (meson range_safe_subset_same fsubset_finsertI)
      then show ?thesis using `L'' |\<subseteq>| L` by auto
    qed
  qed
qed

lemma range_safe_disj:
  "\<forall>L. range_safe s m l = Some L \<longrightarrow> s |\<inter>| L = {||}"(is "?P s m l")
proof (induction rule: range_safe.induct[where ?P = ?P])
  case (1 s m l)
  show ?case
  proof (rule allI, rule impI)
    fix L
    assume "range_safe s m l = Some L "
    then show "s |\<inter>| L = {||}"
    proof (cases rule: range_safe_obtains)
      case (1 v)
      then show ?thesis by simp
    next
      case (2 xs)
      moreover from 2 have
        *: "\<forall>x \<in> set xs. \<forall>L. range_safe (finsert l s) m x = Some L \<longrightarrow> finsert l s |\<inter>| L = {||}"
        using 1(1) by simp
      ultimately show ?thesis using fold_disj[of xs "range_safe (finsert l s) m" s _ L] by blast
    qed
  qed
qed

lemma range_range:
  assumes "range_safe s0 m l1 = Some L1"
      and "range_safe s1 m l1 = Some L2"
    shows "L1 = L2"
  using assms
  by (metis inf_sup_ord(1) range_safe_disj range_safe_subset_same option.inject)

lemma range_safe_prefix:
  assumes "prefix m m'"
      and "range_safe s m l = Some L"
    shows "range_safe s m' l = Some L"
  using assms
proof (induction s m' l arbitrary: L rule: range_safe.induct)
  case (1 s' m' l)

  from 1(3) show ?case
  proof (cases rule: range_safe_obtains)
    case *: (1 v)
    then have "m' $ l = Some (mdata.Value v)" using 1(2) unfolding prefix_def nth_safe_def
      by (simp split:if_split_asm add: nth_append)
    then show ?thesis using * by (simp add:case_memory_def) 
  next
    case (2 xs)
    then have m'_l: "m' $ l = Some (mdata.Array xs)" using 1(2) unfolding prefix_def nth_safe_def
      by (simp split:if_split_asm add: nth_append)
    moreover have
      "fold (\<lambda>x y. y \<bind> (\<lambda>y'. range_safe (finsert l s') m x \<bind> (\<lambda>l. Some (l |\<union>| y')))) xs (Some {|l|})
      = fold (\<lambda>x y. y \<bind> (\<lambda>y'. range_safe (finsert l s') m' x \<bind> (\<lambda>l. Some (l |\<union>| y')))) xs (Some {|l|})"
      (is "fold (?P m) xs (Some {|l|}) = fold (?P m') xs (Some {|l|})")
    proof (rule take_all1)
      show "\<forall>n\<le>length xs. fold (?P m) (take n xs) (Some {|l|}) = fold (?P m') (take n xs) (Some {|l|})"
      proof (rule allI, rule impI)
        fix n
        assume "n \<le> length xs"
        then show "fold (?P m) (take n xs) (Some {|l|}) = fold (?P m') (take n xs) (Some {|l|})"
        proof (induction n)
          case 0
          then show ?case by simp
        next
          case (Suc n)
          from Suc(2) have "n < length xs" by auto
          moreover from 2(3) obtain x
            where *: "fold (?P m) (take n xs) (Some {|l|}) \<bind>
              (\<lambda>y'. range_safe (finsert l s') m (xs ! n) \<bind> (\<lambda>l. Some (l |\<union>| y'))) = Some x"
            using fold_some_take_some[OF _ \<open>n < length xs\<close>] by metis
          moreover have "?P m' (xs ! n) (fold (?P m') (take n xs) (Some {|l|})) = Some x"
          proof -
            from * obtain x' y' where **: "range_safe (finsert l s') m (xs ! n) = Some x'"
              and ***: "(fold (?P m) (take n xs) (Some {|l|})) = Some y'"
              and ****: "x = (x' |\<union>| y')"
              apply (cases "range_safe (finsert l s') m (xs ! n)")
              apply (auto simp del: range_safe.simps)
              apply (cases "fold (?P m) (take n xs) (Some {|l|})")
              by (auto simp del: range_safe.simps)
            moreover from 1(1)[OF 2(1) m'_l _ _ 1(2), of "(xs ! n)"]
            have "range_safe (finsert l s') m' (xs ! n) = Some x'"
             and "(fold (?P m') (take n xs) (Some {|l|})) = Some y'"
             using ** *** nth_mem Suc.IH \<open>n < length xs\<close> by auto
            ultimately show ?thesis by simp
          qed
          ultimately show ?case using
            fold_take[of "n" xs "?P m" "(Some {|l|})"]
            fold_take[of "n" xs "?P m'" "(Some {|l|})"]
            by simp
        qed
      qed
    qed
    ultimately show ?thesis using 2 by (simp add:case_memory_def)
  qed
qed

lemma range_safe_locations:
  assumes "range_safe s m l = Some L"
      and "locations m xs l = Some L'"
    shows "L' |\<subseteq>| L"
  using assms
proof (induction xs arbitrary: l L' L s)
  case Nil
  then show ?case by auto
next
  case (Cons i "is")
  then obtain as i' l' L''
  where "m$l = Some (mdata.Array as)"
    and "to_nat i = Some i'"
    and l2: "as $ i' = Some l'"
    and l3: "locations m is l' = Some L''"
    and l4: "L' = (finsert l L'')"
    using locations_obtain[OF Cons(3)] by blast
  then have *:
    "fold (\<lambda>x y. y \<bind> (\<lambda>y'. (range_safe (finsert l s) m x) \<bind> (\<lambda>l. Some (l |\<union>| y')))) as (Some {|l|})
    = Some L"
    using range_safe_obtains[OF Cons(2)] by fastforce
  moreover from l2 have "l' \<in> set as" unfolding nth_safe_def by (auto split:if_split_asm)
  ultimately obtain L0 where **: "range_safe (finsert l s) m l' = Some L0" and "L0 |\<subseteq>| L"
    using fold_some_subs by metis
  moreover from * have "l |\<in>| L" using fold_some[OF *] by simp
  moreover have "L'' |\<subseteq>| L0" by (rule Cons(1)[OF ** l3])
  ultimately show ?case using l4 by simp
qed

lemma range_safe_l_in_L:
  assumes "range_safe s m l = Some L"
      and "x |\<in>| L"
      and "m $ x = Some (mdata.Array xs)"
      and "l' \<in> set xs"
    shows "l' |\<in>| L"
  by (smt (verit, del_insts) antisym_conv2 assms(1,2,3,4) range_safe_in_subs range_safe_obtains_subset range_safe_subs pfsubsetD)

lemma range_safe_marray_lookup:
  assumes "xs \<noteq> []"
      and "range_safe s m l = Some L"
      and "marray_lookup m xs l = Some (l', ys, i)"
      and "ys $ i = Some l''"
    shows "l'' |\<in>| L"
  using assms 
proof (induction "xs" arbitrary: l L s rule: list_nonempty_induct)
  case (single x)
  then obtain ms i''
    where "m $ l = Some (mdata.Array ms)"
      and "to_nat x = Some i''"
      and 0: "(l', ys, i) = (l, ms, i'')"
    using marray_lookup_obtain_single by blast
  then have
    *: "fold (\<lambda>x y. y \<bind> (\<lambda>y'. (range_safe (finsert l s) m x) \<bind> (\<lambda>l. Some (l |\<union>| y')))) ms (Some {|l|})
    = Some L"
    using range_safe_obtains[OF single(1)] by fastforce
  moreover from single(3) 0 have "l'' \<in> set ms" unfolding nth_safe_def by (auto split:if_split_asm)
  ultimately obtain L0
    where **: "range_safe (finsert l s) m l'' = Some L0"
      and "L0 |\<subseteq>| L"
    using fold_some_subs by metis
  moreover have "l'' |\<in>| L0" using range_safe_subs[OF **] by simp
  ultimately show ?case by auto
next
  case (cons x xs)
  then obtain x' xs'
    where xs_def: "xs = x' # xs'"
    by (meson list.exhaust)
  with cons have *: "marray_lookup m (x # x' # xs') l = Some (l', ys, i)" by simp
  then obtain ms i'' l'''
    where "m $ l = Some (mdata.Array ms)"
      and "vtype_class.to_nat x = Some i''"
      and l3: "ms $ i'' = Some l'''"
      and l4: "marray_lookup m xs l''' = Some (l', ys, i)"
    using marray_lookup_obtain_multi xs_def by blast
  then have
    *: "fold (\<lambda>x y. y \<bind> (\<lambda>y'. (range_safe (finsert l s) m x) \<bind> (\<lambda>l. Some (l |\<union>| y')))) ms (Some {|l|})
    = Some L"
    using range_safe_obtains[OF cons(3)] by fastforce
  moreover from cons l3 have "l''' \<in> set ms" unfolding nth_safe_def by (auto split:if_split_asm)
  ultimately obtain L0
    where **: "range_safe (finsert l s) m l''' = Some L0"
      and "L0 |\<subseteq>| L"
    using fold_some_subs by metis
  moreover have "l'' |\<in>| L0" by (rule cons.IH[OF ** l4 cons(5)])
  ultimately show ?case by auto
qed

lemma range_safe_mlookup:
  assumes "range_safe s m l = Some L"
      and "mlookup m xs l = Some l'"
    shows "l' |\<in>| L"
proof (cases xs)
  case Nil
  then show ?thesis using assms range_safe_subs
    using mlookup_obtain_empty by blast
next
  case (Cons x xs)
  then obtain a xs' i i'
  where "marray_lookup m (x#xs) l = Some (a, xs', i)"
    and "xs' $ i = Some i'"
    and "l' = i'"
    using mlookup_obtain_nempty1 assms(2) by blast
  then show ?thesis using range_safe_marray_lookup[of "x # xs"]
    by (metis assms(1) list.distinct(1))
qed

lemma mlookup_range_safe_subs:
  assumes "mlookup m is l = Some l'"
      and "range_safe s m l' = Some L"
      and "range_safe s' m l = Some L'"
    shows "L |\<subseteq>| L'"
  using assms
proof (induction "is" arbitrary: l L')
  case Nil
  then show ?case
    by (metis fempty_fsubsetI fset_eq_fsubset range_safe_subset_same mlookup_obtain_empty option.inject)
next
  case (Cons i "is")
  then obtain ls i' l''
    where ls_def: "m$l = Some (mdata.Array ls)"
      and "to_nat i = Some i'"
      and l''_def: "ls $ i' = Some l''"
      and "mlookup m is l'' = Some l'"
    using mlookup_obtain_nempty2[OF Cons(2)] by blast
  moreover obtain L'' where "range_safe s' m l'' = Some L''" and "L'' |\<subseteq>| L'"
  proof -
    from Cons(4) have
      *: "fold (\<lambda>x y. y \<bind> (\<lambda>y'. range_safe (finsert l s') m x \<bind> (\<lambda>l. Some (l |\<union>| y')))) ls (Some {|l|})
      = Some L'"
      using range_safe_obtains ls_def by fastforce
    then obtain L''
      where "range_safe (finsert l s') m l'' = Some L'' \<and> L'' |\<subseteq>| L'"
      using fold_some_subs[OF *] l''_def nth_in_set by metis
    then show ?thesis using range_safe_subset_same[of "finsert l s'"] that[of L''] by blast
  qed
  ultimately show ?case using Cons(1)[OF _ Cons(3)] by blast
qed

lemma mlookup_range_safe_some:
  assumes "mlookup m is l = Some l'"
      and "range_safe s m l = Some L"
    shows "\<exists>x. m $l' = Some x"
  using assms
proof (induction "is" arbitrary: l L)
  case Nil
  then have "range_safe s m l = Some L" by simp
  then show ?case
  proof (cases rule: range_safe_obtains)
    case (1 v)
    then show ?thesis using Nil by simp
  next
    case (2 xs)
    then show ?thesis using Nil by simp
  qed
next
  case (Cons i "is")
  from Cons(2) show ?case
  proof (cases rule:mlookup_obtain_nempty2)
    case (1 ls i' l'')
    with Cons(3) have
      "(fold (\<lambda>x y. y \<bind> (\<lambda>y'. (range_safe (finsert l s) m x) \<bind> (\<lambda>l. Some (l |\<union>| y')))) ls (Some {|l|}))
      = Some L"
      by (simp add:case_memory_def split: if_split_asm) 
    moreover have "l'' \<in> set ls" using 1 nth_in_set by fast
    ultimately obtain L' where "range_safe (finsert l s) m l'' = Some L'" and "L' |\<subseteq>| L"
      using fold_some_subs[of "range_safe (finsert l s) m" ls "Some {|l|}" L] using 1 by blast
    then have "range_safe s m l'' = Some L'" unfolding range_safe_prefix
      using range_safe_subset_same by blast
    then show ?thesis using Cons(1)[of l''] 1 by simp
  qed
qed

lemma noloops:
  assumes "mlookup m (i # is) l = Some l'"
      and "range_safe s m l = Some L"
      and "range_safe s m l' = Some L'"
    shows "l |\<notin>| L'"
proof (rule ccontr)
  assume "\<not> l |\<notin>| L'"

  from assms obtain ls
    where ls_def: "m$l = Some (mdata.Array ls)"
    by (meson locations_obtain mlookup_locations_some)
  then have
    L_def: "fold (\<lambda>x y. y \<bind> (\<lambda>y'. (range_safe (finsert l s) m x) \<bind> (\<lambda>l. Some (l |\<union>| y'))))
      ls (Some {|l|}) = Some L"
  using range_safe_obtains[OF assms(2)] by auto

  from ls_def obtain i' l''
    where l''_def: "ls $ i' = Some l''"
      and "mlookup m is l'' = Some l'"
    using mlookup_obtain_nempty2[OF assms(1)] by (metis mdata.inject(2) option.inject)
  moreover from l''_def have "l'' \<in> set ls" unfolding nth_safe_def by (auto split:if_split_asm)
  then obtain L''
    where L''_def: "range_safe (finsert l s) m l'' = Some L''"
    using fold_some_subs[OF L_def] by blast
  then have "range_safe s m l'' = Some L''"
    using range_safe_subset_same [of "finsert l s" m l'' L'']
    by blast
  ultimately have "L' |\<subseteq>| L''" using mlookup_range_safe_subs[OF _ assms(3)] by simp
  moreover have "l |\<notin>| L''" using range_safe_disj L''_def by blast
  ultimately show False using `\<not> l |\<notin>| L'` by auto
qed

definition range where "range \<equiv> range_safe {||}"

lemma range_subs:
  assumes "range m l = Some X"
  shows "l |\<in>| X"
  using assms range_safe_subs range_def by metis

lemma range_subs2:
  assumes "range m l = Some X"
  shows "fset X \<subseteq> loc m"
  using assms range_def range_safe_subs2 by metis

lemma range_same:
  assumes "range m l = Some L"
      and "\<forall>l'|\<in>|L. m' $ l' = m $ l'"
    shows "range m' l = Some L"
  using assms range_def range_safe_same by metis

lemma range_prefix:
  assumes "prefix m m'"
    and "range m l = Some L"
  shows "range m' l = Some L"
  using assms range_safe_prefix
  by (metis range_def)

lemma range_safe_mlookup_range:
  assumes "range_safe s m l = Some L"
    and "mlookup m xs l = Some l'"
  shows "\<exists>L'. range m l' = Some L' \<and> L' |\<subseteq>| L"
  using assms
proof (induction xs arbitrary: l L s)
  case Nil
  then show ?case
    by (metis bot.extremum range_def range_safe_subset_same mlookup.simps(1) option.inject order_refl)
next
  case (Cons a xs)
  then obtain ls i' l''
    where *: "m$l = Some (mdata.Array ls)"
      and **: "to_nat a = Some i'"
      and ***: "ls $ i' = Some l''"
      and "mlookup m xs l'' = Some l'"
    using mlookup_obtain_nempty2 by blast
  moreover from Cons(2) have
    "fold (\<lambda>x y. y \<bind> (\<lambda>y'. range_safe (finsert l s) m x \<bind> (\<lambda>l. Some (l |\<union>| y')))) ls (Some {|l|})
    = Some L"
    using range_safe_obtains[OF Cons(2)] * ** *** by auto
  then obtain L''
    where "range_safe (finsert l s) m l'' = Some L''"
      and "L'' |\<subseteq>| L"
    using fold_some_subs[of "range_safe (finsert l s) m" ls "(Some {|l|})" L l''] *** 
    by (meson nth_in_set)
  ultimately show ?case using Cons(1) by blast
qed

lemma range_locations:
  assumes "range m l = Some L"
      and "locations m xs l = Some L'"
    shows "L' |\<subseteq>| L"
  using assms range_safe_locations
  by (metis range_def)

lemma range_safe_in_range:
  assumes "range_safe s m l = Some L"
      and "l' |\<in>| L"
      and "m $ l' = Some (mdata.Array xs)"
      and "xs $ i = Some i'"
    shows "\<exists>L'. range m i' = Some L' \<and> L' |\<subseteq>| L"
  using assms
proof (induction arbitrary: L rule:range_safe.induct[where ?a0.0 = s and ?a1.0 = m and ?a2.0 = l])
  case (1 s m l)
  from 1(2) show ?case
  proof (cases rule: range_safe_obtains)
    case (1 v)
    then show ?thesis
      using "1.prems"(2,3) by auto
  next
    case (2 xs)
    then consider
       (eq) "l' = l"
      | (2) i L'
      where "i < length xs"
        and "range_safe (finsert l s) m (xs ! i) = Some L'"
        and "l' |\<in>| L'"
      using fold_union_in[of "range_safe (finsert l s) m" xs "{|l|}" L l'] 1(3)
      by blast
    then show ?thesis
    proof (cases)
      case eq
      then have "xs $ i = Some i'" using 1 2 by simp
      then have "i' \<in> set xs" using nth_in_set by fast
      then obtain A
        where "range_safe (finsert l s) m i' = Some A"
          and "A |\<subseteq>| L"
        using 2(3) fold_some_subs[of "range_safe (finsert l s) m"] by blast
      then show ?thesis
        by (metis range_def range_safe_subset_same fempty_fsubsetI)
    next
      case 22: 2
      have "xs!i \<in> set xs" using 22 by simp
      moreover have "L' |\<subseteq>| L" using 22(2) fold_some_subs[OF 2(3) `xs!i \<in> set xs`] by simp
      ultimately show ?thesis using 1(1)[OF 2(1,2) _ _ 22(2,3) 1(4,5)] by fast
    qed
  qed
qed

lemma range_safe_prefix_in_range:
  assumes "range_safe s m l = Some L"
      and "l' |\<in>| L"
      and "m $ l' = Some (mdata.Array xs)"
      and "xs $ i = Some i'"
      and "prefix m m'"
      and "range m' i' = Some L'"
  shows "range m i' = Some L'"
proof -
  from assms obtain L' where "range m i' = Some L'" using range_safe_in_range by blast
  then show ?thesis using assms(5,6)
    by (metis range_prefix)
qed

lemma range_mlookup:
  assumes "range m l = Some L"
      and "mlookup m xs l = Some l'"
    shows "l' |\<in>| L"
  using assms range_safe_mlookup
  by (metis range_def)

lemma mupdate_range_subset:
  assumes "range m l = Some (the (range m l))"
      and "m' = m[l':= mdata.Value v]"
      and "l' < length m"
    shows "\<exists>L. range m' l = Some L \<and> L |\<subseteq>| the (range m l)"
proof -
  have
    "\<forall>l'|\<in>|the (range_safe {||} m l).
      (\<exists>xs. m' $ l' = Some (mdata.Array xs) \<and> m $ l' = Some (mdata.Array xs))
      \<or> (\<exists>xs. m' $ l' = Some (mdata.Value xs))"
  proof rule
    fix l'' assume *: "l'' |\<in>| the (range_safe {||} m l)"
    show
      "(\<exists>xs. m' $ l'' = Some (mdata.Array xs) \<and> m $ l'' = Some (mdata.Array xs))
      \<or> (\<exists>xs. m' $ l'' = Some (mdata.Value xs))"
    proof (cases "l''=l'")
      case True
      then show ?thesis using assms by (simp add:nth_safe_def)
    next
      case False
      then show ?thesis
        using assms(1,2) range_safe_subs2[of "{||}" m l "(the (range_safe {||} m l))"] *
        by (auto intro: mdata.exhaust simp add:nth_safe_def range_def loc_def)
    qed
  qed
  then show ?thesis
    using assms(1) range_safe_subs3[of "{||}" m l "(the (range_safe {||} m l))" m']
    by (simp add: range_def)
qed

section \<open>Copy from Memory\<close>

function read_safe :: "location fset \<Rightarrow> 'v memory \<Rightarrow> location \<Rightarrow> 'd option" where
  "read_safe s m l = 
   (if l |\<in>| s then None else
      case_memory m l
        (\<lambda>v. Some (Value v))
        (\<lambda>xs. those (map (read_safe (finsert l s) m) xs) \<bind> Some \<circ> Array))"
by pat_completeness auto
termination
  apply (relation "measure (\<lambda>(s,m,_). card ({0..length m} - fset s))")
  using card_less_card by auto

lemma read_safe_cases:
  assumes "read_safe s m l = Some c"
  obtains (basic) v
    where "m $ l = Some (mdata.Value v)"
      and "l |\<notin>| s"
      and "c = Value v"
    | (array) xs as
    where "l |\<notin>| s"
      and "m $ l = Some (mdata.Array xs)"
      and "those (map (read_safe (finsert l s) m) xs) = Some as"
      and "c = Array as"
  using assms
  apply (cases "m $ l", auto split:if_split_asm mdata.split_asm simp add:case_memory_def)
  by (case_tac "those (map (read_safe (finsert l s) m) x2)") auto

lemma read_safe_array:
  assumes "m0 $ l1 = Some (mdata.Array ls)"
      and "read_safe s m0 l1 = Some cd1"
      and "ls $ i' = Some l''"
      and cd'_def: "read_safe (finsert l1 s) m0 l'' = Some cd'"
  obtains cs
    where "cd1 = Array cs"
      and "cs $ i' = Some cd'"
      and "length cs = length ls"
  using assms
  apply (auto simp add:case_memory_def split:if_split_asm)
  apply (case_tac "those (map (read_safe (finsert l1 s) m0) ls)",auto)
  by (metis (no_types, lifting) bind.bind_lunit cd'_def map_eq_imp_length_eq those_map_nth those_some_map)

lemma read_safe_update_value:
  assumes "read_safe s m l = Some cd"
      and "m' = m[l' := mdata.Value v]"
    shows "\<exists>cd'. read_safe s m' l = Some cd'"
proof -
  {fix s
    have
      "\<forall>cd m'. read_safe s m l = Some cd \<longrightarrow> m' = m[l' := mdata.Value v]
       \<longrightarrow> (\<exists>cd'. read_safe s m' l = Some cd')" (is "?P s m l")
  proof (induction rule:read_safe.induct[where ?P="?P"])
    case i: (1 s m' l)
    show ?case
    proof (rule, rule, rule, rule)
      fix cd m''
      assume 1: "read_safe s m' l = Some cd"
         and 2: "m'' = m'[l' := mdata.Value v]"
      from 1 
      show "\<exists>cd'. read_safe s m'' l = Some cd'"
      proof (cases rule: read_safe_cases)
        case (basic v)
        then show ?thesis
        proof (cases "l=l'")
          case True
          then show ?thesis using 1 2
            by (auto simp add: case_memory_def nth_safe_def split:if_split_asm)
        next
          case False
          then have "m'' $ l = Some (mdata.Value v)"
            using basic(1) 2 unfolding nth_safe_def by (auto split:if_split_asm)
          then show ?thesis using 1
            by (auto simp add: case_memory_def)
        qed
      next
        case (array xs as)
        then show ?thesis
        proof (cases "l=l'")
          case True
          then show ?thesis using 1 2
            by (auto simp add: case_memory_def nth_safe_def split:if_split_asm)
        next
          case False
          then have "m'' $ l = Some (mdata.Array xs)"
            using array(2) 2 unfolding nth_safe_def by (auto split:if_split_asm)
          moreover have "\<exists>as. those (map (read_safe (finsert l s) m'') xs) = Some as"
          proof -
            have "\<forall>x cd. x \<in> set xs \<and>
             read_safe (finsert l s) m' x = Some cd \<longrightarrow>
             (\<exists>cd'. read_safe (finsert l s) m'' x = Some cd')"
            using i[OF array(1,2)] 2 by blast
            then have "\<forall>x. x \<in> set xs \<longrightarrow> (\<exists>cd'. read_safe (finsert l s) m'' x = Some cd')"
              using those_map_none[OF array(3)] by simp
            then show ?thesis
              using those_map_some_some[of xs "read_safe (finsert l s) m''"] by auto
          qed
          ultimately show ?thesis using array(1)
            by (auto simp add: case_memory_def)
        qed
      qed
    qed
  qed}
  then show ?thesis using assms by metis
qed

lemma read_safe_subset_same:
  assumes "read_safe s m l = Some x"
    and "s' |\<subseteq>| s"
  shows "read_safe s' m l = Some x"
  using assms
proof (induction arbitrary: s x rule:read_safe.induct)
  case (1 s' m l)
  show ?case
    apply (auto split:if_split_asm option.split_asm mdata.split_asm simp add: case_memory_def)
    using 1 apply auto[1]
    apply (case_tac "m$l") apply auto
    using 1 apply (auto split:if_split_asm option.split_asm mdata.split_asm simp add: case_memory_def)[1]
    apply (case_tac "a") apply auto
    using 1 apply (auto split:if_split_asm option.split_asm mdata.split_asm simp add: case_memory_def)[1]
    using 1(1)[of _ _ "finsert l s"] 1(2) 1(3)
    apply (auto simp del: read_safe.simps split:if_split_asm option.split_asm mdata.split_asm simp add: case_memory_def)[1]
    by (smt (verit) "1.IH" bind_eq_Some_conv comp_apply data.read_safe_cases finsert_mono mdata.distinct(1)
        mdata.inject(2) option.inject those_map_eq those_map_none)
qed

lemma read_safe_some_same:             
  assumes "m $ l1 = m $ l2"
      and "read_safe s1 m l1 = Some cd1"
      and "read_safe s2 m l2 = Some cd2"
    shows "cd1 = cd2"
  using assms
proof (induction arbitrary: s2 cd1 cd2 l2 rule:read_safe.induct)
  case (1 s1 m l1)
  from 1(3)
  show ?case
  proof (cases rule: read_safe_cases)
    case basic1: (basic v1)
    from 1(4)
    show ?thesis
    proof (cases rule: read_safe_cases)
      case _: (basic v2)
      then show ?thesis using basic1(1,3) 1(2) by simp
    next
      case (array xs as)
      then show ?thesis using basic1(1,3) 1(2) by simp
    qed
  next
    case array1: (array xs1 as1)
    then have
      IH:"\<And>x cd1 s2 l2 cd2.
        x \<in> set xs1
        \<Longrightarrow> read_safe (finsert l1 s1) m x = Some cd1
        \<Longrightarrow> read_safe s2 m l2 = Some cd2
        \<Longrightarrow> m $ x = m $ l2
        \<Longrightarrow> cd1 = cd2"
      using 1(1) by blast
    from 1(4)
    show ?thesis
    proof (cases rule: read_safe_cases)
      case (basic v2)
      then show ?thesis using array1(2) 1(2) by simp
    next
      case array2: (array xs2 as2)
      then have "xs1 = xs2" using 1(2) array1(2) by simp
      moreover have
        "those (map (read_safe (finsert l1 s1) m) xs1)
         = those (map (read_safe (finsert l2 s2) m) xs1)"
      proof (rule those_map_eq)
        show "\<forall>x\<in>set xs1. \<forall>y. read_safe (finsert l1 s1) m x = Some y
          \<longrightarrow> read_safe (finsert l2 s2) m x = Some y"
        proof (rule, rule, rule)
          fix x y
          assume "x \<in> set xs1"
             and "read_safe (finsert l1 s1) m x = Some y"
          moreover obtain cd where "read_safe (finsert l2 s2) m x = Some cd" 
            using those_map_none[OF array2(3)] \<open>xs1 = xs2\<close> \<open>x \<in> set xs1\<close> by auto
          ultimately show "read_safe (finsert l2 s2) m x = Some y"
            using IH[of x y "(finsert l2 s2)" x] by auto
        qed
      next
        show "\<forall>x\<in>set xs1. read_safe (finsert l1 s1) m x \<noteq> None"
          using those_map_none[OF array1(3)] by blast
      qed
      ultimately have "Array as1 = Array as2" using array1(3) array2(3) by simp
      then show ?thesis using array1(4) array2(4) by simp
    qed
  qed
qed

lemma read_safe_prefix:
  assumes "prefix m m'"
      and "read_safe s m l = Some c"
    shows "read_safe s m' l = Some c"
proof -
  have "\<forall>m' c. prefix m m' \<and> read_safe s m l = Some c
        \<longrightarrow> read_safe s m' l = Some c" (is "?PROP m s l")
  proof (induction rule:read_safe.induct [where ?P="\<lambda>s m l. ?PROP m s l"])
    case (1 s m l)
    show ?case
    proof (rule allI, rule allI, rule impI, erule conjE)
      fix m' c
      assume *: "prefix m m'" and **: "read_safe s m l = Some c"
      then have "l < length m" using nth_safe_length[of m l]
        by (auto split:option.split_asm if_split_asm simp add:case_memory_def)
      then have ***: "m'$l = m $ l" using * unfolding prefix_def
        by (metis length_append nth_append nth_safe_some trans_less_add1)
      
      from **
      consider x
        where "\<not> l |\<in>| s"
          and "m $ l = Some (mdata.Value x)"
          and "c = Value x"
        | xs'
        where "\<not> l |\<in>| s"
          and "m $ l = Some (mdata.Array xs')"
          and "Some c = those (map (read_safe (finsert l s) m) xs') \<bind> Some \<circ> Array"
        using that
        by (auto split:option.split_asm mdata.split_asm if_split_asm simp add:case_memory_def)
      then show "read_safe s m' l = Some c"
      proof cases
        case 1
        then show ?thesis using ***
          by (auto split:option.split mdata.split if_split_asm simp add:case_memory_def)
      next
        case 2
        then obtain ar
          where "c = Array ar"
            and "those (map (read_safe (finsert l s) m) xs') = Some ar"
          by (smt (verit, ccfv_SIG) bind_eq_Some_conv comp_apply option.inject)
        then have "\<forall>x\<in>set xs'. read_safe (finsert l s) m x \<noteq> None"
          using those_map_none by blast
        moreover from 1[OF 2(1) 2(2)] have
          IH: "\<forall>x \<in> set xs'. (\<forall>c. read_safe (finsert l s) m x = Some c
          \<longrightarrow> read_safe (finsert l s) m' x = Some c)"
          using * by blast
        ultimately have
          "those (map (read_safe (finsert l s) m) xs')
          = those (map (read_safe (finsert l s) m') xs')"
          using those_map_eq by blast
        moreover have "m' $ l = Some (mdata.Array xs')" using *** 2(2) by auto
        ultimately show ?thesis using 2 by (auto simp add:case_memory_def)
      qed
    qed
  qed
  then show ?thesis using assms by blast
qed

lemma mlookup_read_safe:
  assumes "mlookup m' xs l = Some x"
      and "m' $ x = Some (mdata.Value v)"
      and "read_safe s m' x = Some a"
    shows "a = Value v"
  using assms by (auto simp add: case_memory_def split:if_split_asm)

lemma mlookup_read_safe_obtain:
  assumes "mlookup m0 (i#is) l1 = Some l1'"
      and "read_safe s m0 l1 = Some cd1"
  obtains ls i' l'' cd'
  where "to_nat i = Some i'"
    and "ls $ i' = Some l''"
    and "mlookup m0 is l'' = Some l1'"
    and "m0 $ l1 = Some (mdata.Array ls)"
    and "read_safe (finsert l1 s) m0 l'' = Some cd'"
proof -
  from assms obtain ls i' l''
    where *: "m0 $ l1 = Some (mdata.Array ls)" 
      and "to_nat i = Some i'"
      and "ls $ i' = Some l''"
      and "mlookup m0 is l'' = Some l1'"
    using mlookup_obtain_nempty2 by blast
  moreover from assms *  `to_nat i = Some i'` `ls $ i' = Some l''`
  obtain cd'
    where cd'_def: "read_safe (finsert l1 s) m0 l'' = Some cd'"
    using those_map_some_nth[of "read_safe (finsert l1 s) m0" ls _ i' l'']
    by (case_tac "those (map (read_safe (finsert l1 s) m0) ls)",
        auto simp add:case_memory_def split:if_split_asm)
  ultimately show ?thesis using that by simp
qed

definition "read = read_safe {||}"

lemma read_some_same:
  assumes "read_safe s m l = Some x"
  shows "read m l = Some x"
  using assms read_safe_subset_same unfolding read_def by blast

lemma read_append:
  assumes "prefix m m'"
      and "read m l = Some c"
    shows "read m' l = Some c"
  using assms read_safe_prefix unfolding read_def
  by blast

section \<open>Copy Memory and Memory Locations\<close>

lemma range_safe_read_safe:
  assumes "range_safe s m l = Some L"
    shows "\<exists>x. read_safe s m l = Some x"
  using assms
proof (induction arbitrary: L rule:range_safe.induct)
  case (1 s m l)
  from 1(2) show ?case
  proof (cases rule:range_safe_obtains)
    case (1 v)
    then show ?thesis by (auto simp add:case_memory_def)
  next
    case (2 xs)
    moreover have "\<exists>x. those (map (read_safe (finsert l s) m) xs) \<bind> Some \<circ> Array = Some x"
    proof -
      from 2(3) have "\<forall>x \<in> set xs. \<exists>y. range_safe (finsert l s) m x = Some y"
        by (metis fold_some_subs)
      then have "\<forall>x \<in> set xs. \<exists>y. read_safe (finsert l s) m x = Some y"
        using 1(1)[OF 2(1,2)] by blast
      then obtain z where "those (map (read_safe (finsert l s) m) xs) = Some z"
        by (metis not_Some_eq those_map_none_none)
      then show ?thesis by simp
    qed
    ultimately show ?thesis by (auto simp add:case_memory_def)
  qed
qed

lemma read_safe_range_safe:
  assumes "read_safe s m l = Some cd"
      and "range_safe s m l = Some L"
      and "\<forall>l'|\<in>|L. m' $ l' = m $ l'"
    shows "read_safe s m' l = Some cd"
  using assms
proof (induction arbitrary: cd L rule: read_safe.induct)
  case (1 s m' l)
  from 1(2) show ?case
  proof (cases rule: read_safe_cases)
    case _: (basic v)
    then show ?thesis using 1 by (auto simp add:case_memory_def)
  next
    case (array v as)
    moreover have "l|\<in>|L" using 1(3)
      apply (auto simp add:case_memory_def)
      using "1.prems"(2) data.range_safe_subs by blast
    then have *: "m' $ l = Some (mdata.Array v)" using array(2) 1(4) by simp
    moreover have "those (map (read_safe (finsert l s) m') v)
                  = those (map (read_safe (finsert l s) m) v)"
    proof -
      have "\<forall>x \<in> set v. read_safe (finsert l s) m' x = read_safe (finsert l s) m x"
      proof
        fix x assume "x \<in> set v"
        moreover from array(3)
        obtain xx where "those (map (read_safe (finsert l s) m) v) = Some xx"
          by (cases "those (map (read_safe (finsert l s) m) v)", auto)
        then obtain c where "read_safe (finsert l s) m x = Some c"
          by (meson `x \<in> set v` not_None_eq those_map_none)
        moreover from array have
          **: "fold
                (\<lambda>x y. y \<bind> (\<lambda>y'. (range_safe (finsert l s) m x) \<bind> (\<lambda>l. Some (l |\<union>| y'))))
                v
                (Some {|l|})
              = Some L"
          using range_safe_obtains[OF 1(3)] by auto
        then obtain L' where "range_safe (finsert l s) m x = Some L'" and "L' |\<subseteq>| L"
          using fold_some_subs[OF **] `x \<in> set v` by auto
        moreover from `L' |\<subseteq>| L` have "\<forall>l'|\<in>|L'. m' $ l' = m $ l'" using 1(4) by blast
        ultimately show "read_safe (finsert l s) m' x = read_safe (finsert l s) m x"
          using 1(1)[OF array(1) *] "1.prems"(3) by auto
      qed
      then show ?thesis
        by (metis map_ext)
    qed
    ultimately show ?thesis by (auto simp add:case_memory_def)
  qed
qed

lemma read_range:
  assumes "read m l = Some cd"
      and "range m l = Some L"
      and "\<forall>l'|\<in>|L. m' $ l' = m $ l'"
    shows "read m' l = Some cd"
  using assms read_safe_range_safe unfolding read_def range_def by blast

lemma read_safe_range_safe_same:
  assumes "read_safe s m1 l = Some x"
      and "range_safe s m1 l = Some L"
      and "\<forall>l |\<in>| s' - s. l |\<notin>| L"
  shows "read_safe s' m1 l = Some x"
  using range_safe_nin_same[OF assms(2,3)] assms(1)
  by (metis read_some_same range_safe_read_safe)

lemma range_read_some:
  assumes "read_safe s m0 l0 = Some cd0"
    shows "\<exists>L. range_safe s m0 l0 = Some L"
  using assms
proof (induction arbitrary: cd0 rule:read_safe.induct)
  case (1 s m l)
  from 1(2) show ?case
  proof (cases rule:read_safe_cases)
    case (basic v)
    then show ?thesis by (auto simp add:case_memory_def)
  next
    case (array xs as)
    moreover have "\<forall>x \<in> set xs. \<exists>L. range_safe (finsert l s) m x = Some L"
    proof
      fix x
      assume "x \<in> set xs"
      moreover obtain cd where "read_safe (finsert l s) m x = Some cd"
        by (meson array(3) calculation set_nth_some those_map_some_nth)
      ultimately show "\<exists>L. range_safe (finsert l s) m x = Some L" using 1(1)
        by (meson array(1,2))
    qed
    ultimately have
      "fold
        (\<lambda>x y. y \<bind> (\<lambda>y'. range_safe (finsert l s) m x \<bind> (\<lambda>l. Some (l |\<union>| y'))))
        xs
        (Some {|l|})
      \<noteq> None"
      using fold_f_set_some[of _ "range_safe (finsert l s) m"] by simp
    then show ?thesis using array by (simp add: case_memory_def)
  qed
qed

lemma read_safe_range_safe_subs:
 assumes "m $ l1' = Some (mdata.Array ls)"
    and "l2 \<in> set ls"
    and "mlookup m is2 l1 = Some l1'"
    and "range_safe s m l1 = Some L1"
    and "read_safe s m l1 = Some cd"
  shows "\<exists>x y. read_safe s m l2 = Some x \<and> range_safe s m l2 = Some y \<and> y |\<subseteq>| L1"
proof -
  from assms(3,4) have "l1' |\<in>| L1" using range_safe_mlookup by blast
  then obtain L1'
    where *: "range_safe s m l1' = Some L1'"
      and "L1' |\<subseteq>| L1"
    using range_safe_in_subs[OF assms(4), of l1'] by auto
  moreover from * have
    "fold
      (\<lambda>x y. y \<bind> (\<lambda>y'. (range_safe (finsert l1' s) m x) \<bind> (\<lambda>l. Some (l |\<union>| y'))))
      ls
      (Some {|l1'|})
    = Some L1'"
  using assms(1,2) by (auto simp add:case_memory_def split:if_split_asm)
  then obtain LL
    where "range_safe (finsert l1' s) m l2 = Some LL"
    and "LL |\<subseteq>| L1'"
  using fold_some_subs[of "range_safe (finsert l1' s) m" ls "Some {|l1'|}" L1'] assms(2) by blast
  then have "range_safe s m l2 = Some LL"
    using range_safe_subset_same by blast
  ultimately show ?thesis using range_safe_read_safe[of s m l2 LL] `LL |\<subseteq>| L1'` by auto
qed

section \<open>Separation Check\<close>

definition disjoint:: "'v memory \<Rightarrow> location fset \<Rightarrow> bool" where
  "disjoint m L \<equiv>
    \<forall>x |\<in>| L. \<forall>xs. m$x = Some (mdata.Array xs)
    \<longrightarrow> (\<forall>i j i' j' L L'.
          i \<noteq> j \<and> xs $ i = Some i' \<and> xs$j = Some j' \<and> range m i' = Some L \<and> range m j' = Some L'
      \<longrightarrow> L |\<inter>| L' = {||})"

lemma disjoint_subs[intro]:
  assumes "L' |\<subseteq>| L"
      and "disjoint m L"
    shows "disjoint m L'"
  using assms unfolding disjoint_def by blast

lemma disjoint_disjoint:
  assumes "disjoint m L"
      and "range m l = Some L"
      and "\<forall>l |\<in>| L. m $ l = m' $ l"
    shows "disjoint m' L"
  unfolding disjoint_def
proof (rule,rule,rule,rule,rule,rule,rule,rule,rule,rule)
  fix x xs i j i' j' La L'
  assume *: "x |\<in>| L"
    and **: "m' $ x = Some (mdata.Array xs)"
    and ***: "i \<noteq> j
              \<and> xs $ i = Some i'
              \<and> xs $ j = Some j'
              \<and> range m' i' = Some La
              \<and> range m' j' = Some L'"
  moreover from * ** have "m $ x = Some (mdata.Array xs)" using assms(3) by auto
  moreover from assms(2) have "La |\<subseteq>| L" using range_safe_in_range[OF _ * **, of "{||}" l i i']
    unfolding range_def using ***
    by (metis assms(3) range_def range_same option.inject)
  with *** have "range m i' = Some La" using range_same[of m' i' La m]
    using assms(3) by auto
  moreover from assms(2) have "L' |\<subseteq>| L" using range_safe_in_range[OF _ * **, of "{||}" l j j']
    unfolding range_def using ***
    by (metis assms(3) range_def range_same option.inject)
  with *** have "range m j' = Some L'" using range_same[of m' j' L' m]
    using assms(3) by auto
  ultimately show "La |\<inter>| L' = {||}" using assms(1) unfolding disjoint_def by blast
qed

lemma disjoint_prefix:
  assumes "fset L \<subseteq> loc m"
      and "prefix m m'"
      and "disjoint m L"
      and "range_safe s m' l = Some L"
    shows "disjoint m' L"
  unfolding disjoint_def
proof (rule,rule,rule,rule,rule,rule,rule,rule,rule,rule)
  fix x xs i j i' j' La L'
  assume *: "x |\<in>| L"
    and **: "m' $ x = Some (mdata.Array xs)"
    and ***: "i \<noteq> j
              \<and> xs $ i = Some i'
              \<and> xs $ j = Some j'
              \<and> range m' i' = Some La
              \<and> range m' j' = Some L'"
  moreover from * ** assms(1,2) have "m $ x = Some (mdata.Array xs)"
    unfolding prefix_def nth_safe_def loc_def by (auto split: if_split_asm simp add: nth_append_left)
  moreover have "La |\<subseteq>| L" using range_safe_in_range[OF assms(4) * **] *** by fastforce
  then have "\<forall>l'|\<in>|La. m $ l' = m' $ l'"
    using assms(1,2) unfolding prefix_def loc_def nth_safe_def by (auto simp add: nth_append_left)
  then have "range m i' = Some La" using range_same[of m' i' La m] using calculation(3) by auto
  moreover have "L' |\<subseteq>| L" using range_safe_in_range[OF assms(4) * **] *** by fastforce
  then have "\<forall>l'|\<in>|L'. m $ l' = m' $ l'" using assms(1,2)
    unfolding prefix_def loc_def nth_safe_def by (auto simp add: nth_append_left)
  then have "range m j' = Some L'" using range_same[of m' j' L' m] using calculation(3) by auto
  moreover have "range m j' = Some L'" using range_same[of m' j' L' m] using calculation(6) by auto
  ultimately show "La |\<inter>| L' = {||}" using assms(3) unfolding disjoint_def by (meson  \<open>x |\<in>| L\<close>)
qed

lemma update_some:
"\<forall>is1 L1 cd1 L3. mlookup m0 is1 l1 = Some l1' \<and>
      m1 $ l1' = m0 $ l2 \<and>
      range_safe s m0 l1 = Some L1 \<and>
      range_safe s m0 l1' = Some L1' \<and>
      range_safe s2 m0 l2 = Some L2 \<and>
      (\<forall>l |\<in>| L1 |-| L1'. m1 $ l = m0 $ l) \<and>
      (\<forall>l |\<in>| L2. m1 $ l = m0 $ l) \<and>
      read_safe s m0 l1 = Some cd1 \<and>
      read_safe s2 m0 l2 = Some cd2 \<and>
      s |\<inter>| L2 = {||} \<and>
      locations m0 is1 l1 = Some L3 \<and>
      L3 |\<inter>| L2 = {||} \<and>
      l1' |\<notin>| L2 \<and>
      disjoint m0 L1
    \<longrightarrow> (\<exists>x. read_safe s m1 l1 = Some x)" (is "?P s m1 l1")
proof (induction rule: read_safe.induct[where ?P = ?P])
  case IH: (1 s m1 l1)
  show ?case
  proof (rule allI, rule allI, rule allI, rule allI, rule impI, (erule conjE)+)
    fix is1 L1 cd1 L3
    assume 1: "mlookup m0 is1 l1 = Some l1'"
       and 3: "m1 $ l1' = m0 $ l2"
       and 4: "range_safe s m0 l1 = Some L1"
       and 5: "range_safe s m0 l1' = Some L1'"
       and 6: "range_safe s2 m0 l2 = Some L2"
       and 7: "\<forall>l |\<in>| L1 |-| L1'. m1 $ l = m0 $ l"
       and 8: "\<forall>l|\<in>|L2. m1 $ l = m0 $ l"
       and 9: "read_safe s m0 l1 = Some cd1"
       and 10: "read_safe s2 m0 l2 = Some cd2"
       and 11: "s |\<inter>| L2 = {||}"
       and 12: "locations m0 is1 l1 = Some L3"
       and 13: "L3 |\<inter>| L2 = {||}"
       and 14: "l1' |\<notin>| L2"
       and 15: "disjoint m0 L1"
    from 9 have "l1 |\<notin>| s" by auto
    show "\<exists>x. read_safe s m1 l1 = Some x"
    proof (cases "m1$l1")
      case None
      show ?thesis
      proof (cases "is1 = []")
        case True
        then have "m1$l1 = m0$l2" using 1 3 by simp
        then show ?thesis using None
          by (metis "10" read_safe_cases option.discI)
      next
        case False
        then obtain iv is1' where "is1=iv#is1'"
          using list.exhaust by auto

        have "l1 |\<in>| L1" using 4 using range_safe_subs by blast
        moreover have "l1 |\<notin>| L1'"
          using 1 `is1=iv#is1'` noloops[of m0 iv is1' l1 l1' s L1 L1'] 4 5 by simp
        ultimately have "m1$l1 = m0$l1" using 7 by blast
        then show ?thesis using 1 None mlookup_start_some `is1=iv#is1'` by fastforce
      qed
    next
      case (Some a)
      then show ?thesis
      proof (cases a)
        case (Value v)
        then show ?thesis using Some `l1 |\<notin>| s` by (simp add:case_memory_def)
      next
        case (Array ls)
        have *: "\<forall>l \<in> set ls. \<exists>x'. read_safe (finsert l1 s) m1 l = Some x'"
        proof
          fix l assume "l \<in> set ls"
          then obtain i where l_def: "ls $ i = Some l" using set_nth_some by fast
          then show "\<exists>x'. read_safe (finsert l1 s) m1 l = Some x'"
          proof (cases "is1 = []")
            case True
            then have "m1$l1 = m0$l2" using 1 3 by simp
            then have "m0$l2 = Some (mdata.Array ls)" using Some Array by simp
            then obtain x y
              where "read_safe s2 m0 l = Some x"
                and "range_safe s2 m0 l = Some y"
                and "y |\<subseteq>| L2"
              using \<open>l \<in> set ls\<close> 6 10 read_safe_range_safe_subs mlookup.simps(1) by blast
            then have "read_safe s2 m1 l = Some x" and "range_safe s2 m1 l = Some y"
              using 8 read_safe_range_safe[of s2 m0 l x y m1]
                range_safe_same[of s2 m0 l y m1] by blast+  
            moreover have "l1 |\<notin>| L2" using 14 1 True by simp
            ultimately have "read_safe (finsert l1 s) m1 l = Some x"
              using 11 `y |\<subseteq>| L2` read_safe_range_safe_same[where ?s' = "finsert l1 s"]
              by blast
            then show ?thesis by simp
          next
            case False
            then obtain iv is1' where "is1=iv#is1'"
              using list.exhaust by auto

            from 12 have "l1 |\<in>| L3" using `is1=iv#is1'` locations_l_in_L by blast
            with 13 have "l1 |\<notin>| L2" by blast

            have "l1 |\<in>| L1" using 4 using range_safe_subs by blast
            moreover have "l1 |\<notin>| L1'"
              using 1 `is1=iv#is1'` noloops[of m0 iv is1' l1 l1' s L1 L1'] 4 5 by simp
            ultimately have "m1$l1 = m0$l1" using 7 by blast

            show ?thesis
            proof (cases "to_nat iv = Some i")
              case True
              then have "mlookup m0 is1' l = Some l1'"
                using 1 Some Array l_def `is1=iv#is1'` `m1$l1 = m0$l1`
                by (cases is1', auto simp add:case_memory_def)
              moreover from 4 
              have
                "fold
                  (\<lambda>x y. y \<bind> (\<lambda>y'. (range_safe (finsert l1 s) m0 x) \<bind> (\<lambda>l. Some (l |\<union>| y'))))
                  ls
                  (Some {|l1|})
                = Some L1"
                using Some Array `m1$l1 = m0$l1` `l1 |\<notin>| s` by (auto simp add:case_memory_def)
              then obtain L1''
                where "range_safe (finsert l1 s) m0 l = Some L1''"
                  and "L1'' |\<subseteq>| L1"
                using fold_some_subs[of "range_safe (finsert l1 s) m0" ls "Some {|l1|}" L1] `l \<in> set ls`
                by blast
              moreover from 9 obtain cd1' where "read_safe (finsert l1 s) m0 l = Some cd1'"
                using Some Array `m1$l1 = m0$l1` `l1 |\<notin>| s`
                apply (auto simp add:case_memory_def)
                using those_map_none[of "read_safe (finsert l1 s) m0"] `l \<in> set ls` by force
              moreover have "range_safe (finsert l1 s) m0 l1' = Some L1'" using 5 \<open>l1 |\<notin>| L1'\<close>
                by (smt (verit, best) finsertE fminusD1 fminusD2 range_safe_nin_same)
              moreover have "l1 |\<notin>| s" using 9 by auto
              moreover from 11 have "finsert l1 s |\<inter>| L2 = {||}" using `l1 |\<notin>| L2` by simp
              moreover from 12 obtain L3'
                where "locations m0 is1' l = Some L3'"
                  and "L3 = finsert l1 L3'"
                using Some Array `is1=iv#is1'` `m1$l1 = m0$l1` l_def True
                apply (cases "to_nat iv",auto simp add:case_memory_def)
                by (case_tac "locations m0 is1' l",auto) 
              moreover from 7 have "\<forall>l|\<in>|L1'' |-| L1'. m1 $ l = m0 $ l"
                using `L1'' |\<subseteq>| L1` by blast
              moreover from 13 have "L3' |\<inter>| L2 = {||}" using `L3 = finsert l1 L3'` by auto
              moreover from 15 have "disjoint m0 L1''" using `L1'' |\<subseteq>| L1` by blast
              moreover have "l1 |\<notin>| L1''"
                by (metis calculation(2) finsert_not_fempty finter_finsert_left range_safe_disj)
              ultimately show ?thesis using IH[OF _ _ `l \<in> set ls`] Some Array 3 6 8 10 14 by auto
            next
              case False
              then obtain i' l'
                where "to_nat iv = Some i'"
                  and "i' \<noteq> i" 
                  and "ls$i' = Some l'"
                by (metis "12" Array Some \<open>is1 = iv # is1'\<close> \<open>m1 $ l1 = m0 $ l1\<close>
                    locations_obtain mdata.inject(2) option.inject)
              moreover have "\<exists>L. range m0 l = Some L"
              proof -
                have "l1 |\<notin>| s" using 9 by auto
                then have
                  "range_safe s m0 l1
                   = fold
                      (\<lambda>x y. y \<bind> (\<lambda>y'. (range_safe (finsert l1 s) m0 x) \<bind> (\<lambda>l. Some (l |\<union>| y'))))
                      ls
                      (Some {|l1|})"
                  using Some Array `m1$l1 = m0$l1` by (auto simp add:case_memory_def)
                with 4 obtain L where "range_safe (finsert l1 s) m0 l = Some L"
                  using fold_f_set_none[OF `l \<in> set ls`, of "range_safe (finsert l1 s) m0"]
                  by fastforce
                then show ?thesis unfolding range_def using range_safe_subset_same by blast
              qed
              then obtain L where L_def: "range m0 l = Some L" by blast
              moreover have "\<exists>L'. range_safe (finsert l1 s) m0 l' = Some L'"
              proof -
                have "l1 |\<notin>| s" using 9 by auto
                then have
                  "range_safe s m0 l1
                  = fold
                      (\<lambda>x y. y \<bind> (\<lambda>y'. (range_safe (finsert l1 s) m0 x) \<bind> (\<lambda>l. Some (l |\<union>| y'))))
                      ls
                      (Some {|l1|})"
                  using Some Array `m1$l1 = m0$l1` by (auto simp add:case_memory_def)
                moreover have "l' \<in> set ls" using `ls$i' = Some l'` nth_in_set by fast
                ultimately obtain L where "range_safe (finsert l1 s) m0 l' = Some L"
                  using fold_f_set_none[of l' _ "range_safe (finsert l1 s) m0"] using 4 by fastforce
                then show ?thesis unfolding range_def using range_safe_subset_same by blast
              qed
              then obtain L' where "range_safe (finsert l1 s) m0 l' = Some L'" by blast
              then have L'_def: "range_safe s m0 l' = Some L'"
                using data.range_safe_subset_same by blast
              then have "range m0 l' = Some L'" unfolding range_def
                using range_safe_subset_same by blast
              ultimately have "(L |\<inter>| L' = {||})"
                using 15 Some Array `m1$l1 = m0$l1` l_def `l1 |\<in>| L1` unfolding disjoint_def by metis
              moreover from 1 have "mlookup m0 is1' l' = Some l1'"
                using Some Array `is1=iv#is1'` `m1$l1 = m0$l1` \<open>ls $ i' = Some l'\<close>
                  \<open>vtype_class.to_nat iv = Some i'\<close> mlookup_obtain_nempty2 by fastforce
              then have "L1' |\<subseteq>| L'" using mlookup_range_safe_subs 5 L'_def by blast
              ultimately have "L |\<inter>| L1' = {||}" by blast
              moreover have "L |\<subseteq>| L1" using L_def 4
              proof -
                from 4 have
                  "fold
                    (\<lambda>x y. y \<bind> (\<lambda>y'. (range_safe (finsert l1 s) m0 x) \<bind> (\<lambda>l. Some (l |\<union>| y'))))
                    ls
                    (Some {|l1|})
                  = Some L1"
                  using Some Array `m1$l1 = m0$l1` `l1 |\<notin>| s` by (auto simp add:case_memory_def)
                then obtain L1''
                  where "range_safe (finsert l1 s) m0 l = Some L1''"
                    and "L1'' |\<subseteq>| L1"
                  using fold_some_subs[of "range_safe (finsert l1 s) m0" ls "Some {|l1|}" L1] `l \<in> set ls`
                  by blast
                then show ?thesis using L_def unfolding range_def
                  by (metis bot.extremum data.range_safe_subset_same option.inject)
              qed
              ultimately have "\<forall>l|\<in>|L. m0$l = m1$l" using 7 by force
              then have "range m1 l = Some L" using L_def
                using range_same by metis
              moreover have "(finsert l1 s) |\<inter>| L = {||}"
              proof -
                from 4 have
                  "fold
                    (\<lambda>x y. y \<bind> (\<lambda>y'. (range_safe (finsert l1 s) m0 x) \<bind> (\<lambda>l. Some (l |\<union>| y'))))
                    ls
                    (Some {|l1|})
                  = Some L1"
                  using Some Array `m1$l1 = m0$l1` `l1 |\<notin>| s` by (auto simp add:case_memory_def)
                then obtain L1''
                  where L1''_def: "range_safe (finsert l1 s) m0 l = Some L1''"
                    and "L1'' |\<subseteq>| L1"
                  using fold_some_subs[of "range_safe (finsert l1 s) m0" ls "Some {|l1|}" L1] `l \<in> set ls`
                    by blast
                moreover have "(finsert l1 s) |\<inter>| L1'' = {||}" using range_safe_disj L1''_def by blast
                ultimately show ?thesis using L_def unfolding range_def
                  by (metis bot.extremum data.range_safe_subset_same option.inject)
              qed
              ultimately have "range_safe (finsert l1 s) m1 l = Some L"
                using range_safe_nin_same[of "{||}"] `l1 |\<notin>| s` `L |\<subseteq>| L1` unfolding range_def by blast
              then show ?thesis using range_safe_read_safe by blast
            qed
          qed
        qed
        have "l1 |\<notin>| s" using 9 by auto
        then show ?thesis using Some Array
          apply (auto simp add:case_memory_def) using * 
          by (smt (verit, del_insts) bind.bind_lunit comp_def not_None_eq those_map_some_some)
      qed
    qed
  qed
qed

lemma update_some_obtains_read:
  assumes "mlookup m0 is1 l1 = Some l1'"
  and "m1 $ l1' = m0 $ l2"
  and "range_safe s0 m0 l1 = Some L1"
  and "range_safe s0 m0 l1' = Some L1'"
  and "range_safe s1 m0 l2 = Some L2"
  and "(\<forall>l |\<in>| L1 |-| L1'. m1 $ l = m0 $ l)"
  and "(\<forall>l |\<in>| L2. m1 $ l = m0 $ l)"
  and "read_safe s0 m0 l1 = Some cd1"
  and "read_safe s1 m0 l2 = Some cd2"
  and "s0 |\<inter>| L2 = {||}"
  and "locations m0 is1 l1 = Some L3"
  and "L3 |\<inter>| L2 = {||}"
  and "l1' |\<notin>| L2"
  and "disjoint m0 L1"
obtains x where "read_safe s0 m1 l1 = Some x"
  using update_some[of m0 l1 l1' m1 l2 s0 L1' s1 L2 cd2] assms
  unfolding range_def read_def 
  by blast

lemma update_some_obtains_range:
  assumes "mlookup m0 is1 l1 = Some l1'"
  and "m1 $ l1' = m0 $ l2"
  and "range_safe s0 m0 l1 = Some L1"
  and "range_safe s0 m0 l1' = Some L1'"
  and "range_safe s1 m0 l2 = Some L2"
  and "(\<forall>l |\<in>| L1 |-| L1'. m1 $ l = m0 $ l)"
  and "(\<forall>l |\<in>| L2. m1 $ l = m0 $ l)"
  and "s0 |\<inter>| L2 = {||}"
  and "locations m0 is1 l1 = Some L3"
  and "L3 |\<inter>| L2 = {||}"
  and "l1' |\<notin>| L2"
  and "disjoint m0 L1"
obtains L where "range_safe s0 m1 l1 = Some L"
proof -
  from assms(3) obtain cd1 where "read_safe s0 m0 l1 = Some cd1"
    using range_safe_read_safe by blast
  moreover from assms(5) obtain cd2 where "read_safe s1 m0 l2 = Some cd2"
    using range_safe_read_safe by blast
  ultimately obtain x where "read_safe s0 m1 l1 = Some x"
    using update_some_obtains_read[OF assms(1,2,3,4,5,6,7) _ _ assms(8, 9,10,11,12)]
    by blast
  then show ?thesis using range_read_some that by blast
qed

lemma disjoint_range_disj:
  assumes "disjoint m0 L"
      and "x |\<in>| L"
      and "m0 $ x = Some (mdata.Array xs)"
      and "m0 $ x = m1 $ x"
      and "\<forall>l \<in> set xs. range m1 l = range m0 l"
    shows
  "\<forall>xs. m1$x = Some (mdata.Array xs)
    \<longrightarrow> (\<forall>i j i' j' L L'.
          i \<noteq> j \<and> xs $ i = Some i' \<and> xs$j = Some j' \<and> range m1 i' = Some L \<and> range m1 j' = Some L'
      \<longrightarrow> L |\<inter>| L' = {||})"
proof (rule allI, rule impI)
  fix xs
  assume "m1 $ x = Some (mdata.Array xs)"
  with assms(1,2,4) have "(\<forall>i j i' j' L L'.
          i \<noteq> j \<and> xs $ i = Some i' \<and> xs$j = Some j' \<and> range m0 i' = Some L \<and> range m0 j' = Some L'
      \<longrightarrow> L |\<inter>| L' = {||})" unfolding disjoint_def by auto
  then show "\<forall>i j i' j' L L'. i \<noteq> j \<and> xs $ i = Some i' \<and> xs $ j = Some j' \<and> range m1 i' = Some L \<and> range m1 j' = Some L' \<longrightarrow> L |\<inter>| L' = {||}"
    using assms(3,5)
    by (metis \<open>m1 $ x = Some (mdata.Array xs)\<close> assms(4) mdata.inject(2) nth_in_set option.inject)
qed

lemma update_some_range_subset:
  assumes "mlookup m0 is1 l1 = Some l1'"
      and "m1 $ l1' = m0 $ l2'"
      and "range_safe s m0 l1 = Some L1"
      and "range_safe s m0 l1' = Some L1'"
      and "range_safe s m0 l2' = Some L2'"
      and "(\<forall>l |\<in>| L1 |-| L1'. m1 $ l = m0 $ l)"
      and "(\<forall>l |\<in>| L2'. m1 $ l = m0 $ l)"
      and "disjoint m0 L1"
      and "range_safe s m1 l1 = Some L"
    shows "L |\<subseteq>| L1 |\<union>| L2'"
  using assms
proof (induction is1 arbitrary: L l1 L1)
  case Nil
  then have "l1 = l1'" by simp
  show ?case
  proof (cases "m1$l1")
    case None
    then show ?thesis
      by (metis Nil.prems(9) range_safe_obtains option.distinct(1))
  next
    case (Some a)
    then show ?thesis
    proof (cases a)
      case (Value x1)
      with Nil(9) Some have "L = {|l1|}" by (simp add:case_memory_def split:if_split_asm)
      moreover from Nil(3) have "l1 |\<in>| L1" using range_safe_subs by blast
      ultimately show ?thesis by auto
    next
      case (Array xs)
      from Nil(3) have "l1 |\<notin>| s" by auto
      with Nil(9) have "fold (\<lambda>x y. y \<bind> (\<lambda>y'. range_safe (finsert l1 s) m1 x \<bind> (\<lambda>l. Some (l |\<union>| y')))) xs (Some {|l1|}) =
        Some L" using Some Array by (simp add:case_memory_def)
      moreover have "\<forall>x\<in>set xs. \<forall>L. range_safe (finsert l1 s) m1 x = Some L \<longrightarrow> fset L \<subseteq> fset (L1 |\<union>| L2')"
      proof (rule ballI, rule allI, rule impI)
        fix x L'
        assume "x \<in> set xs" and "range_safe (finsert l1 s) m1 x = Some L'"
        moreover have "m1 $ l1 = m1 $ l2'"
        proof -
          have "m0 $ l2' = m1 $ l2'"
            by (metis Nil.prems(5,7) range_safe_subs)
          then show ?thesis using Nil(2) \<open>l1 = l1'\<close> by simp
        qed
        moreover have L2'_def: "range_safe s m1 l2' = Some L2'"
          using Nil.prems(5,7) range_safe_same by blast
        ultimately show "fset L' \<subseteq> fset (L1 |\<union>| L2')"
          by (metis Array Some range_safe_obtains_subset less_eq_fset.rep_eq range_range sup.coboundedI2)
      qed
      moreover have "fset {|l1|} \<subseteq> fset (L1 |\<union>| L2')"
        by (metis Nil.prems(3) finsert_absorb finsert_is_funion less_eq_fset.rep_eq range_safe_subs sup.cobounded1
            sup.coboundedI1)
      ultimately show ?thesis using fold_subs by fast
    qed
  qed
next
  case (Cons i is1')
  obtain ls
    where ls_def: "m0 $ l1 = Some (mdata.Array ls)"
    using Cons(2)
    by (cases is1',auto simp add:case_memory_def split:option.split_asm mdata.split_asm)
  then have m1_ls: "m1 $ l1 = Some (mdata.Array ls)"
    by (metis Cons.prems(1,3,4,6) range_safe_subs fminus_iff noloops)

  have "l1 |\<in>| L1" using Cons.prems(3) range_safe_subs by blast

  obtain i'' where i''_def: "to_nat i = Some i''" and "i'' < length ls"
    using Cons.prems(1) mlookup_obtain_nempty2
    by (metis ls_def mdata.inject(2) nth_safe_length option.inject)
  then have "ls $i'' = Some (ls ! i'')" by simp

  have "l1 |\<notin>| s"
    using Cons.prems(3) by force
  with Cons(10) m1_ls have "fold (\<lambda>x y. y \<bind> (\<lambda>y'. range_safe (finsert l1 s) m1 x \<bind> (\<lambda>l. Some (l |\<union>| y')))) ls (Some {|l1|}) = Some L" by (simp add:case_memory_def)
  moreover have "\<forall>x\<in>set ls. \<forall>L. range_safe (finsert l1 s) m1 x = Some L \<longrightarrow> fset L \<subseteq> fset (L1 |\<union>| L2')"
  proof
    fix x assume "x \<in> set ls"
    then obtain i' where x_def: "ls ! i' = x" and "i'<length ls"
      by (meson in_set_conv_nth)
    then have "ls $ i' = Some x" by simp 
    then show "\<forall>L. range_safe (finsert l1 s) m1 x = Some L \<longrightarrow> fset L \<subseteq> fset (L1 |\<union>| L2')"
    proof (cases "i' = i''")
      case True
      show ?thesis
      proof (rule allI, rule impI)
        fix LLL assume "range_safe (finsert l1 s) m1 x = Some LLL"
        then have "range_safe s m1 x = Some LLL"
          using data.range_safe_subset_same by blast
        moreover from True have "mlookup m0 is1' x = Some l1'" using Cons(2) \<open>ls ! i' = x\<close> \<open>to_nat i = Some i''\<close>
          by (metis \<open>ls $ i'' = Some (ls ! i'')\<close> ls_def mdata.inject(2) mlookup_obtain_nempty2 option.inject)
        moreover obtain LL where "range_safe s m0 x = Some LL" and "LL |\<subseteq>| L1"
          by (meson Cons.prems(3) \<open>x \<in> set ls\<close> range_safe_obtains_subset fsubset_finsertI range_safe_subset_same ls_def)
        moreover have "\<forall>l|\<in>|LL |-| L1'. m1 $ l = m0 $ l"
          using Cons.prems(6) calculation(4) by blast
        moreover have "disjoint m0 LL"
          by (meson Cons.prems(8) calculation(4) disjoint_subs)
        ultimately have "LLL |\<subseteq>| LL |\<union>| L2'" using Cons(1)[OF _ Cons(3) _ Cons(5) Cons(6) _ Cons(8)] by blast
        then show "fset LLL \<subseteq> fset (L1 |\<union>| L2')"
          using \<open>LL |\<subseteq>| L1\<close> by blast
      qed
    next
      case False
      then obtain LL where "range_safe (finsert l1 s) m0 x = Some LL" and "LL |\<subseteq>| L1"
        using Cons.prems(3) \<open>x \<in> set ls\<close> range_safe_obtains_subset ls_def by blast
      then have "range m0 x = Some LL"
          by (metis bot.extremum data.range_def data.range_safe_subset_same)
      moreover obtain LLL where LL_def: "range_safe (finsert l1 s) m0 (ls ! i'') = Some LLL" and "LLL |\<subseteq>| L1"
        using Cons.prems(3)
        by (meson \<open>ls $ i'' = Some (ls ! i'')\<close> range_safe_obtains_subset ls_def nth_in_set)
      then have LLL_def: "range m0 (ls ! i'') = Some LLL"
          by (metis bot.extremum data.range_def data.range_safe_subset_same)
      moreover have "LL |\<inter>| LLL = {||}" using Cons(9) unfolding disjoint_def using False i''_def x_def \<open>l1 |\<in>| L1\<close> ls_def \<open>ls $i'' = Some (ls ! i'')\<close>  \<open>ls $ i' = Some x\<close>
      LL_def LLL_def using calculation(1) by blast
      moreover have "L1' |\<subseteq>| LLL"
      proof -
        have "mlookup m0 is1' (ls ! i'') = Some l1'"
          using Cons.prems(1) \<open>ls $ i'' = Some (ls ! i'')\<close> i''_def ls_def mlookup_obtain_nempty2 by fastforce
        moreover from LL_def have "range_safe s m0 (ls ! i'') = Some LLL"
          using data.range_safe_subset_same by blast
        ultimately show ?thesis using mlookup_range_safe_subs[OF _ Cons(5)] by blast
      qed
      ultimately have "LL |\<inter>| L1' = {||}" by auto
      with \<open>LL |\<subseteq>| L1\<close> have "\<forall>l |\<in>| LL. m1 $ l = m0 $ l" using Cons(7) by blast
      then have "range_safe (finsert l1 s) m1 x = Some LL" using Cons(10)
        using \<open>range_safe (finsert l1 s) m0 x = Some LL\<close> data.range_safe_same by blast
      with \<open>LL |\<subseteq>| L1\<close> show ?thesis by auto
    qed
  qed
  moreover from \<open>l1 |\<in>| L1\<close> have "fset {|l1|} \<subseteq> fset (L1 |\<union>| L2')" by simp
  ultimately show ?case using fold_subs[of ls "range_safe (finsert l1 s) m1" "fset (L1 |\<union>| L2')" "{|l1|}" L]
    by blast
qed

lemma disjoint_update:
  assumes "mlookup m0 is1 l1 = Some l1'"
      and "m1 $ l1' = m0 $ l2'"
      and "range_safe s m0 l1 = Some L1"
      and "range_safe s m0 l1' = Some L1'"
      and "range_safe s m0 l2' = Some L2'"
      and "(\<forall>l |\<in>| L1 |-| L1'. m1 $ l = m0 $ l)"
      and "(\<forall>l |\<in>| L2'. m1 $ l = m0 $ l)"
      and "disjoint m0 L1"
      and "disjoint m0 L2'"
      and "range_safe s m1 l1 = Some L"
      and "L1 |-| L1' |\<inter>| L2' = {||}"
    shows "disjoint m1 L"
  using assms
proof (induction is1 arbitrary: L l1 L1)
  case Nil
  then have "l1 = l1'" by simp
  show ?case
  proof (cases "m1$l1")
    case None
    then show ?thesis
      by (metis Nil.prems(10) range_safe_obtains option.distinct(1))
  next
    case (Some a)
    then show ?thesis
    proof (cases a)
      case (Value x1)
      with Nil(10) Some have "L = {|l1|}" by (simp add:case_memory_def split:if_split_asm)
      then show ?thesis
        by (simp add: Some Value disjoint_def)
    next
      case (Array xs)
      show ?thesis unfolding disjoint_def
      proof (rule ballI)
        fix x
        assume "x |\<in>| L"
        moreover have "l1 |\<notin>| s" using Nil by auto
        with Nil(10) have "fold (\<lambda>x y. y \<bind> (\<lambda>y'. range_safe (finsert l1 s) m1 x \<bind> (\<lambda>l. Some (l |\<union>| y')))) xs
                  (Some {|l1|}) = Some L"  using Some Array by (simp add:case_memory_def)
        ultimately consider "x = l1" | n L'' where "n<length xs" and "range_safe (finsert l1 s) m1 (xs ! n) = Some L''" "x |\<in>| L''"
          using fold_union_in by fast
        then show "\<forall>xs. m1 $ x = Some (mdata.Array xs) \<longrightarrow>
              (\<forall>i j i' j' L L'.
                  i \<noteq> j \<and> xs $ i = Some i' \<and> xs $ j = Some j' \<and> range m1 i' = Some L \<and> range m1 j' = Some L' \<longrightarrow>
                  L |\<inter>| L' = {||})"
        proof cases
          case 1
          show ?thesis
          proof (rule allI, rule impI, (rule allI)+, rule impI)
            fix xs' i j i' j' L L'
            assume "m1 $ x = Some (mdata.Array xs')"
              and *: "i \<noteq> j \<and> xs' $ i = Some i' \<and> xs' $ j = Some j' \<and> range m1 i' = Some L \<and> range m1 j' = Some L'"
            moreover have "range m0 i' = Some L"
            proof -
              obtain L0 where "range_safe (finsert l2' s) m0 i' = Some L0" and "L0 |\<subseteq>| L2'" using Nil(5)
                by (metis "1" \<open>l1 = l1'\<close> assms(2) calculation(1,2) range_safe_obtains_subset nth_in_set) 
              then have "range m0 i' = Some L0"
                by (metis bot.extremum data.range_def data.range_safe_subset_same)
              moreover from \<open>L0 |\<subseteq>| L2'\<close> have "\<forall>l |\<in>| L0. m1 $ l = m0 $ l" using Nil(7) by blast
              ultimately show ?thesis using * range_same by metis
            qed
            moreover have "range m0 j' = Some L'" 
            proof -
              obtain L0 where "range_safe (finsert l2' s) m0 j' = Some L0" and "L0 |\<subseteq>| L2'" using Nil(5)
                by (metis "1" \<open>l1 = l1'\<close> assms(2) calculation(1,2) range_safe_obtains_subset nth_in_set) 
              then have "range m0 j' = Some L0"
                by (metis bot.extremum data.range_def data.range_safe_subset_same)
              moreover from \<open>L0 |\<subseteq>| L2'\<close> have "\<forall>l |\<in>| L0. m1 $ l = m0 $ l" using Nil(7) by blast
              ultimately show ?thesis using * range_same by metis
            qed
            ultimately show "L |\<inter>| L' = {||}" using Some Array  Nil(9) unfolding disjoint_def
              by (metis "1" \<open>l1 = l1'\<close> assms(2,5) range_safe_subs)
          qed
        next
          case 2
          moreover from Nil(5) obtain LL where LL_def: "range_safe (finsert l2' s) m0 (xs ! n) = Some LL" and "LL |\<subseteq>| L2'" using Some Array Nil(2) \<open>l1 = l1'\<close>
            by (metis calculation(1) range_safe_obtains_subset nth_mem)
          then have "range_safe (finsert l2' s) m1 (xs ! n) = Some LL"
            by (metis assms(7) data.range_safe_same finsert_fsubset mk_disjoint_finsert)
          ultimately have "LL = L''" using range_range by blast
          with Nil(9) 2 LL_def \<open>LL |\<subseteq>| L2'\<close> Some Array
          have *: "\<forall>x|\<in>|L2'. \<forall>xs. m0 $ x = Some (mdata.Array xs) \<longrightarrow> (\<forall>i j i' j' L L'.
          i \<noteq> j \<and> xs $ i = Some i' \<and> xs$j = Some j' \<and> range m0 i' = Some L \<and> range m0 j' = Some L'
      \<longrightarrow> L |\<inter>| L' = {||})" unfolding disjoint_def
            by (metis)
          show ?thesis
          proof (rule allI, rule impI, (rule allI)+, rule impI)
            fix xs' i j i' j' L L'
            assume 00: "m1 $ x = Some (mdata.Array xs')"
              and **: "i \<noteq> j \<and> xs' $ i = Some i' \<and> xs' $ j = Some j' \<and> range m1 i' = Some L \<and> range m1 j' = Some L'"
            moreover have "x |\<in>|L2'"
              using "2"(3) \<open>LL = L''\<close> \<open>LL |\<subseteq>| L2'\<close> by blast
            moreover have "m0 $ x = Some (mdata.Array xs')"
              using "00" assms(7) calculation(3) by auto
            moreover have "range m0 i' = Some L"
            proof -
              obtain L0 where "range_safe (finsert l2' s) m0 i' = Some L0" and "L0 |\<subseteq>| L2'" using Nil(5) Some Array 2 LL_def \<open>LL |\<subseteq>| L2'\<close>
                by (smt (verit, ccfv_threshold) "**" \<open>LL = L''\<close> range_safe_l_in_L calculation(1) fsubset_trans range_safe_in_subs
                    nth_in_set)
              then have "range m0 i' = Some L0"
                by (metis bot.extremum data.range_def data.range_safe_subset_same)
              moreover from \<open>L0 |\<subseteq>| L2'\<close> have "\<forall>l |\<in>| L0. m1 $ l = m0 $ l" using Nil(7) by blast
              ultimately show ?thesis using ** range_same by metis
            qed
            moreover have "range m0 j' = Some L'"
            proof -
              obtain L0 where "range_safe (finsert l2' s) m0 j' = Some L0" and "L0 |\<subseteq>| L2'" using Nil(5) Some Array 2 LL_def \<open>LL |\<subseteq>| L2'\<close>
                by (smt (verit, ccfv_threshold) "**" \<open>LL = L''\<close> range_safe_l_in_L calculation(1) fsubset_trans range_safe_in_subs
                    nth_in_set)
              then have "range m0 j' = Some L0"
                by (metis bot.extremum data.range_def data.range_safe_subset_same)
              moreover from \<open>L0 |\<subseteq>| L2'\<close> have "\<forall>l |\<in>| L0. m1 $ l = m0 $ l" using Nil(7) by blast
              ultimately show ?thesis using ** range_same by metis
            qed
            ultimately show "L |\<inter>| L' = {||}" using * by blast
          qed
        qed
      qed
    qed
  qed
next
  case (Cons i is1')
  obtain ls
    where ls_def: "m0 $ l1 = Some (mdata.Array ls)"
    using Cons(2)
    by (cases is1',auto simp add:case_memory_def split:option.split_asm mdata.split_asm)
  then have m1_ls: "m1 $ l1 = Some (mdata.Array ls)"
    by (metis Cons.prems(1,3,4,6) range_safe_subs fminus_iff noloops)

  have "l1 |\<in>| L1" using Cons.prems(3) range_safe_subs by blast

  obtain i'' where i''_def: "to_nat i = Some i''" and "i'' < length ls"
    using Cons.prems(1) mlookup_obtain_nempty2
    by (metis ls_def mdata.inject(2) nth_safe_length option.inject)
  then have "ls $i'' = Some (ls ! i'')" by simp

  show ?case unfolding disjoint_def
  proof
    fix x
    assume "x |\<in>| L"
    show
      "\<forall>xs. m1 $ x = Some (mdata.Array xs)
        \<longrightarrow> (\<forall>i j i' j' L L'.
              i \<noteq> j
              \<and> xs $ i = Some i'
              \<and> xs $ j = Some j'
              \<and> range m1 i' = Some L
              \<and> range m1 j' = Some L'
              \<longrightarrow> L |\<inter>| L' = {||})"
    proof (rule allI, rule impI)
      fix xs
      assume xs_def: "m1 $ x = Some (mdata.Array xs)"

      have "l1 |\<notin>| s"
        by (metis Cons.prems(3) \<open>l1 |\<in>| L1\<close> fminus_iff fminus_triv range_safe_disj)
      then have
        "fold
          (\<lambda>x y. y \<bind> (\<lambda>y'. (range_safe (finsert l1 s) m1 x) \<bind> (\<lambda>l. Some (l |\<union>| y'))))
          ls
          (Some {|l1|})
         = Some L"
        using Cons(11) by (simp add:case_memory_def m1_ls)
      with \<open>x |\<in>| L\<close> consider
         (eq) "x = l1"
        | (2) i' L'
        where "i' < length ls"
          and "range_safe (finsert l1 s) m1 (ls ! i') = Some L'"
          and "x |\<in>| L'"
        using fold_union_in[of "range_safe (finsert l1 s) m1" ls "{|l1|}" L x]
        by blast
      then show
        "\<forall>i j i' j' L L'.
          i \<noteq> j \<and>
          xs $ i = Some i' \<and>
          xs $ j = Some j' \<and>
          range m1 i' = Some L \<and>
          range m1 j' = Some L'
        \<longrightarrow> L |\<inter>| L' = {||}"
      proof cases
        case eq
        then have "ls = xs" using xs_def m1_ls by simp

        {fix i0 j L0 L' i0' i' j'
          assume "i0 = i''"
              and "j \<noteq> i''"
              and "i' < length ls"
              and *: "i0 \<noteq> j \<and> xs $ i0 = Some i0' \<and> xs $ j = Some j' \<and> range m1 i0' = Some L0 \<and> range m1 j' = Some L'"
        have "\<forall>x |\<in>| L0. x |\<notin>| L'"
        proof
          fix x
          assume "x |\<in>| L0"
          
          have "mlookup m0 is1' i0' = Some l1'"
            using Cons(2) i''_def ls_def \<open>i0 = i''\<close> \<open>ls $ i'' = Some (ls ! i'')\<close> \<open>ls = xs\<close> *
          by (cases "is1'", auto simp add:case_memory_def)
          moreover obtain Li'
            where Li'_def: "range_safe (finsert l1 s) m0 i0' = Some Li'"
              and "Li' |\<subseteq>| L1"
            using range_safe_obtains_subset[OF Cons(4) ls_def] using \<open>i' < length ls\<close> \<open>ls = xs\<close> * by (metis nth_in_set)
          then have "range_safe s m0 i0' = Some Li'"
            by (meson fsubset_finsertI range_safe_subset_same)
          moreover have "\<forall>l|\<in>|Li' |-| L1'. m1 $ l = m0 $ l" using Cons(7) \<open>Li' |\<subseteq>| L1\<close> by auto
          moreover obtain LL' where "range_safe s m1 i0' = Some LL'" and "LL' |\<subseteq>| L"
            using range_safe_obtains_subset[OF Cons(11) m1_ls] \<open>ls = xs\<close> *
            by (metis fsubset_finsertI range_safe_subset_same nth_in_set)
          moreover have "disjoint m0 Li'"
            using Cons.prems(8) \<open>Li' |\<subseteq>| L1\<close> by auto
          ultimately consider "x |\<in>|Li'" | "x |\<in>| L2'"
            using update_some_range_subset[OF _ Cons(3) _ Cons(5,6) _ Cons(8), of is1' "i0'" Li' LL']
            by (metis "*" \<open>x |\<in>| L0\<close> fsubsetD funion_iff range_def range_range)
          then show "x |\<notin>| L'"
          proof cases
            case 1
            moreover have "L' |\<inter>| Li' = {||}"
            proof -
              obtain LL where LL_def: "range m0 j' = Some LL" and "LL |\<subseteq>| L1"
                by (metis "*" Cons.prems(3) \<open>ls = xs\<close> range_safe_in_range range_safe_subs ls_def)
              moreover have "\<forall>l|\<in>|LL. m1 $ l = m0 $ l"
              proof -
                have "m0 $ l1 = Some (mdata.Array xs)"
                  by (simp add: \<open>ls = xs\<close> ls_def)
                moreover have "range m0 i0' = Some Li'"
                  by (metis Li'_def fempty_fsubsetI range_def range_safe_subset_same)
                ultimately have "LL |\<inter>| Li' = {||}"
                  using \<open>l1 |\<in>| L1\<close> * LL_def Cons(9) unfolding disjoint_def by blast
                moreover have "L1' |\<subseteq>| Li'" using mlookup_range_safe_subs[OF _ Cons(5)]
                  using \<open>range_safe s m0 i0' = Some Li'\<close> \<open>mlookup m0 is1' i0' = Some l1'\<close> by blast
                ultimately have "LL |\<inter>| L1' = {||}" by auto
                then show ?thesis using Cons(7) \<open>LL |\<subseteq>| L1\<close> by auto
              qed
              ultimately have "range m0 j' = Some L'" using range_safe_same[of "{||}" m0 j' LL m1] *
                using range_def by argo
              moreover have "m0 $ l1 = Some (mdata.Array xs)"
                by (simp add: \<open>ls = xs\<close> ls_def)
              moreover have "range m0 i0' = Some Li'"                                                     
                by (metis Li'_def fempty_fsubsetI range_def range_safe_subset_same)
              ultimately show "L' |\<inter>| Li' = {||}"
                using \<open>l1 |\<in>| L1\<close> * LL_def Cons(9) unfolding disjoint_def by blast
            qed
            ultimately show ?thesis by blast
          next
            case 2
            moreover have "L' |\<subseteq>| L1 |-| L1'"
            proof -
              obtain LL where LL_def: "range m0 j' = Some LL" and "LL |\<subseteq>| L1"
                by (metis "*" Cons.prems(3) \<open>ls = xs\<close> range_safe_in_range range_safe_subs ls_def)
              moreover have "LL |\<inter>| L1' = {||}"
              proof -
                have "m0 $ l1 = Some (mdata.Array xs)"
                  by (simp add: \<open>ls = xs\<close> ls_def)
                moreover have "range m0 i0' = Some Li'"
                  by (metis Li'_def fempty_fsubsetI range_def range_safe_subset_same)
                ultimately have "LL |\<inter>| Li' = {||}"
                  using \<open>l1 |\<in>| L1\<close> * LL_def Cons(9) unfolding disjoint_def by blast
                moreover have "L1' |\<subseteq>| Li'" using mlookup_range_safe_subs[OF _ Cons(5)]
                  using \<open>range_safe s m0 i0' = Some Li'\<close> \<open>mlookup m0 is1' i0' = Some l1'\<close> by blast
                ultimately have "LL |\<inter>| L1' = {||}" by auto
                then show ?thesis using Cons(7) \<open>LL |\<subseteq>| L1\<close> by auto
              qed
              ultimately have "\<forall>l|\<in>|LL. m1 $ l = m0 $ l"
                using Cons.prems(6) by blast
              then have "range m0 j' = Some L'" using range_safe_same[of "{||}" m0 j' LL m1] *
                using LL_def range_def by argo
              then show ?thesis
                using LL_def \<open>LL |\<inter>| L1' = {||}\<close> \<open>LL |\<subseteq>| L1\<close> by auto
            qed
            ultimately show ?thesis using Cons(12) by auto
          qed
        qed
        then have "L0 |\<inter>| L' = {||}" by auto
        } note lem=this

        show ?thesis
        proof ((rule allI)+, rule impI)
          fix i0 j i0' j' L0 L'
          assume *: "i0 \<noteq> j \<and> xs $ i0 = Some i0' \<and> xs $ j = Some j' \<and> range m1 i0' = Some L0 \<and> range m1 j' = Some L'"
          then consider
            (1) "i0 \<noteq> j" and "i0 \<noteq> i''" and "j \<noteq> i''" |
            (2) "i0 = i''" and "j \<noteq> i''" |
            (3) "j = i''" and "i0 \<noteq> i''"
            by blast
          then show "L0 |\<inter>| L' = {||}"
          proof cases
            case 1
            from *
              have "i0 \<noteq> j"
               and "xs $ i0 = Some i0'"
               and "xs $ j = Some j'"
               and "range m1 i0' = Some L0"
               and "range m1 j' = Some L'"
              by simp+
            then have "i0' \<in> set xs" and "j' \<in> set xs" by (auto simp add: nth_in_set)
            then obtain Li'
              where Li'_def: "range_safe (finsert l1 s) m0 i0' = Some Li'"
                and "Li' |\<subseteq>| L1" using range_safe_obtains_subset[OF Cons(4) ls_def, of "i0'"]
            using \<open>ls = xs\<close> by auto
            then have "range m0 i0' = Some Li'"
              unfolding range_def using data.range_safe_subset_same by blast
            moreover obtain Li''
              where Li''_def: "range_safe (finsert l1 s) m0 j' = Some Li''"
              and "Li'' |\<subseteq>| L1" using range_safe_obtains_subset[OF Cons(4) ls_def, of "j'"]
            using \<open>ls = xs\<close> \<open>j' \<in> set xs\<close> by auto
            then have "range m0 j' = Some Li''"
              unfolding range_def using data.range_safe_subset_same by blast
            moreover have "Li' |\<inter>| Li'' = {||}"
              using "*" Cons.prems(8) \<open>l1 |\<in>| L1\<close> \<open>ls = xs\<close> calculation(1,2) disjoint_def ls_def by blast
            moreover have "range m1 i0' = range m0 i0'" and "range m1 j' = range m0 j'"
            proof -
              have *:"mlookup m0 is1' (ls ! i'') = Some l1'"
                using Cons(2) i''_def ls_def \<open>ls $ i'' = Some (ls ! i'')\<close>
                by (cases "is1'", auto simp add:case_memory_def)
              moreover obtain LL where LL_def: "range_safe s m0 (ls ! i'') = Some LL"
              and "LL |\<subseteq>| L1" using range_safe_obtains_subset[OF Cons(4) ls_def]
                by (metis \<open>ls $ i'' = Some (ls ! i'')\<close> fsubset_finsertI range_safe_subset_same nth_in_set)
              moreover have "L1' |\<subseteq>| LL" using mlookup_range_safe_subs[OF * Cons(5)] LL_def by simp
              moreover have "LL |\<inter>| Li' = {||}"
              proof -
                from LL_def have "range m0 (ls ! i'') = Some LL"
                  by (metis fempty_fsubsetI range_def range_safe_subset_same)
                then show ?thesis using Cons(9) \<open>range m0 i0' = Some Li'\<close> unfolding disjoint_def
                  using "1"(2) \<open>ls $ i'' = Some (ls ! i'')\<close> \<open>ls = xs\<close> \<open>xs $ i0 = Some i0'\<close> ls_def \<open>l1 |\<in>| L1\<close> by blast
              qed
              ultimately have "Li' |\<inter>| L1' = {||}" by auto
              then have "\<forall>l |\<in>| Li'. m1 $ l = m0 $ l" using Cons(7) \<open>range m0 i0' = Some Li'\<close> \<open>Li' |\<subseteq>| L1\<close> by blast
              then show "range m1 i0' = range m0 i0'"
                by (metis \<open>range m0 i0' = Some Li'\<close> data.range_same)

              from LL_def have "range m0 (ls ! i'') = Some LL"
                by (metis fempty_fsubsetI range_def range_safe_subset_same)   
              then have "LL |\<inter>| Li'' = {||}"
                using "1"(3) \<open>ls $ i'' = Some (ls ! i'')\<close> \<open>ls = xs\<close> \<open>xs $ j = Some j'\<close> ls_def \<open>l1 |\<in>| L1\<close>  Cons(9) \<open>range m0 j' = Some Li''\<close>
                unfolding disjoint_def by blast
              then have "Li'' |\<inter>| L1' = {||}" using \<open>L1' |\<subseteq>| LL\<close> by auto
              then have "\<forall>l |\<in>| Li''. m1 $ l = m0 $ l"
                using Cons(7) \<open>range m0 j' = Some Li''\<close> \<open>Li'' |\<subseteq>| L1\<close> by blast
              then show "range m1 j' = range m0 j'" by (metis \<open>range m0 j' = Some Li''\<close> data.range_same)
            qed
            ultimately show ?thesis
              by (simp add: \<open>range m1 i0' = Some L0\<close> \<open>range m1 j' = Some L'\<close>)
          next
            case 2
            show ?thesis using lem 2
              using "*" \<open>i'' < length ls\<close> by blast
          next
            case 3
            show ?thesis using lem 3
              using "*" \<open>i'' < length ls\<close> by blast
          qed
        qed
      next
        case 2
        show ?thesis
        proof (cases "i'' = i'")
          case True
          with Cons(2) have "mlookup m0 is1' (ls ! i'') = Some l1'"
            using Cons(2) i''_def ls_def \<open>ls $ i'' = Some (ls ! i'')\<close>
            by (cases "is1'", auto simp add:case_memory_def)
          moreover obtain LL
            where "range_safe (finsert l1 s) m0 (ls ! i'') = Some LL"
              and "LL |\<subseteq>| L1"
            using range_safe_obtains_subset[OF Cons(4) ls_def] using "2"(1) True nth_mem by blast
          then have "range_safe s m0 (ls ! i'') = Some LL"
            by (meson fsubset_finsertI range_safe_subset_same)
          moreover have "\<forall>l|\<in>|LL |-| L1'. m1 $ l = m0 $ l" using \<open>LL |\<subseteq>| L1\<close> Cons(7) by auto
          moreover have "disjoint m0 LL"  using \<open>LL |\<subseteq>| L1\<close> Cons(9) by auto
          moreover obtain LL'
            where "range_safe s m1 (ls ! i'') = Some LL'"
              and "LL' |\<subseteq>| L"
            using range_safe_obtains_subset[OF Cons(11) m1_ls]
            by (metis \<open>ls $ i'' = Some (ls ! i'')\<close> fsubset_finsertI range_safe_subset_same nth_in_set)
          moreover have "LL |-| L1' |\<inter>| L2' = {||}" using Cons(12)
            using \<open>LL |\<subseteq>| L1\<close> by blast
          ultimately have "disjoint m1 LL'" using Cons(1)[of "ls ! i''", OF _ Cons(3) _ Cons(5,6) _ Cons(8) _ Cons(10)]
            by simp
          then show ?thesis
            using \<open>LL' |\<subseteq>| L\<close> "2"(2,3) True \<open>range_safe s m1 (ls ! i'') = Some LL'\<close> disjoint_def range_range xs_def by blast
        next
          case False
          moreover obtain Li'
            where Li'_def: "range_safe (finsert l1 s) m0 (ls ! i') = Some Li'"
              and "Li' |\<subseteq>| L1" using 2(1) range_safe_obtains_subset[OF Cons(4) ls_def, of "ls ! i'"]
            by auto
          then have "range m0 (ls ! i') = Some Li'"
            unfolding range_def using data.range_safe_subset_same by blast
          moreover obtain Li''
            where Li''_def: "range_safe (finsert l1 s) m0 (ls ! i'') = Some Li''"
            using i''_def range_safe_obtains_subset[OF Cons(4) ls_def, of "ls ! i''"] \<open>i'' < length ls\<close> by auto
          then have "range m0 (ls ! i'') = Some Li''"
            unfolding range_def using data.range_safe_subset_same by blast
          moreover have "ls $i' = Some (ls ! i')" by (simp add: "2"(1))
          ultimately have "Li' |\<inter>| Li'' = {||}"
            using Cons(9) Li''_def \<open>l1 |\<in>| L1\<close> ls_def \<open>ls $i'' = Some (ls ! i'')\<close>
            unfolding disjoint_def by blast
          moreover have "L1' |\<subseteq>| Li''"
          proof -
            have "mlookup m0 is1' (ls ! i'') = Some l1'"
              using Cons(2) i''_def ls_def \<open>ls $ i'' = Some (ls ! i'')\<close>
              by (cases "is1'", auto simp add:case_memory_def)
            moreover from Li''_def have "range_safe s m0 (ls ! i'') = Some Li''"
              using data.range_safe_subset_same by blast
            ultimately show ?thesis using mlookup_range_safe_subs[OF _ Cons(5)] by simp
          qed
          ultimately have "Li' |\<inter>| L1' = {||}" by blast
          then have *: "\<forall>x |\<in>| Li'. m1 $ x = m0 $ x" using Cons(7) \<open>Li' |\<subseteq>| L1\<close> by blast
          then have "Li' = L'" using 2(2) range_safe_same[OF Li'_def] by auto
          moreover from \<open>Li' = L'\<close> have "x |\<in>| Li'" using 2(3) by simp
          ultimately have "m1 $ x = m0 $ x" using * by simp
          moreover have "\<forall>l \<in> set xs. range m1 l = range m0 l"
          proof
            fix l assume "l \<in> set xs"
            then have "l |\<in>| L'" using range_safe_l_in_L[OF 2(2,3) xs_def] by simp
            then obtain X
              where "range_safe (finsert l1 s) m1 l = Some X"
                and "X |\<subseteq>| L'"
              using range_safe_in_subs[OF 2(2)] by blast
            moreover from \<open>X |\<subseteq>| L'\<close> have "X |\<subseteq>|Li'" using \<open>Li' = L'\<close> by simp
            then have "\<forall>x |\<in>| X. m1 $ x = m0 $ x" using * by auto
            ultimately have "range_safe (finsert l1 s) m1 l = range_safe (finsert l1 s) m0 l"
              using range_safe_same[of "finsert l1 s" m1 l] by auto
            then show "range m1 l = range m0 l"
              by (metis \<open>range_safe (finsert l1 s) m1 l = Some X\<close>
                  fempty_fminus fempty_iff range_def range_safe_nin_same)
          qed
          moreover have "x |\<in>| L1" using "2"(3) \<open>Li' |\<subseteq>| L1\<close> \<open>Li' = L'\<close> by auto
          moreover have "m0 $ x = Some (mdata.Array xs)"
            using \<open>m1 $ x = Some (mdata.Array xs)\<close> calculation(1) by auto
          ultimately have
            "\<forall>xs. m1 $ x = Some (mdata.Array xs)
              \<longrightarrow> (\<forall>i j i' j' L L'.
                    i \<noteq> j
                    \<and> xs $ i = Some i'
                    \<and> xs $ j = Some j'
                    \<and> range m1 i' = Some L
                    \<and> range m1 j' = Some L'
                    \<longrightarrow> L |\<inter>| L' = {||})"
            using disjoint_range_disj[OF Cons(9), of x xs m1] by simp
          then show ?thesis using \<open>m1 $ x = Some (mdata.Array xs)\<close> by blast
        qed
      qed
    qed
  qed
qed

end

section \<open>Array Data\<close>

datatype 'v adata =
  is_Value: Value (vt: "'v")
| is_Array: Array (ar: "'v adata list")

abbreviation case_adata where "case_adata cd vf af \<equiv> adata.case_adata vf af cd"

global_interpretation a_data: data adata.Value adata.Array
  defines aread_safe = a_data.read_safe
      and aread = a_data.read
      and arange_safe = a_data.range_safe
      and arange = a_data.range
      and adisjoint = a_data.disjoint
  .

section \<open>Array Lookup\<close>

text \<open>
  alookup is cd navigates array cd according to the index sequence is.
\<close>
fun alookup :: "'v::vtype list \<Rightarrow> 'v adata \<Rightarrow> 'v adata option" where
  "alookup [] s = Some s"
| "alookup (i # is) (adata.Array xs) = to_nat i \<bind> ($) xs \<bind> alookup is"
| "alookup _ _ = None"

lemma alookup_obtains_some:
  assumes "alookup is s = Some sd"
  obtains "is = []" and "sd = s"
  | i is' i' xs sd' where "is = i # is'" and "s = adata.Array xs" and "to_nat i = Some i'" and "xs $ i' = Some sd'" and "alookup is' sd' = Some sd" 
  using assms
  apply (cases s)
  apply (auto)
  using alookup.elims apply blast
  apply (cases "is",auto)
  apply (case_tac "to_nat a",auto)
  by (case_tac "x2$aa",auto)

lemma alookup_append:
  "alookup (xs1@xs2) cd = alookup xs1 cd \<bind> alookup xs2"
proof (induction xs1 arbitrary: cd)
  case Nil
  then show ?case by simp
next
  case (Cons a xs1)
  then show ?case
  proof (cases cd)
    case (Value x1)
    then show ?thesis by auto
  next
    case (Array x2)
    then show ?thesis using Cons
    apply (case_tac "to_nat a", auto)
    apply (case_tac "x2$aa")
    by auto
  qed
qed

lemma alookup_empty_some:
    shows "alookup [] cd = Some cd"
  by simp

lemma alookup_nempty_some:
  assumes "to_nat x = Some i"
      and "cd = adata.Array a"
      and "i < length a"
      and "alookup xs (a!i) = Some cd'"
    shows "alookup (x # xs) cd = Some cd'"
  using assms
  by simp

proposition alookup_same: "(\<forall>xs. alookup xs cd1 = alookup xs cd2) \<equiv> cd1 = cd2"
proof (induction cd1)
  case (Value x1)
  then show ?case
  proof (induction cd2)
    case (Value x2)
    then show ?case apply (auto)
    proof -
      assume "(\<forall>xs. alookup xs (adata.Value x1) = alookup xs (adata.Value x2))"
      then show "x1 = x2"
      proof (rule contrapos_pp)
        assume "x1 \<noteq> x2"
        then have "alookup [] (adata.Value x1) \<noteq> alookup [] (adata.Value x2)" by simp
        then show "\<not> (\<forall>xs. alookup xs (adata.Value x1) = alookup xs (adata.Value x2))" by blast
      qed
    qed
  next
    case (Array x)
    show ?case apply (auto)
    proof -
      have "alookup [] (adata.Value x1) \<noteq> alookup [] (adata.Array x)" by simp
      then show "\<exists>xs. alookup xs (adata.Value x1) \<noteq> alookup xs (adata.Array x)" by blast
    qed
  qed
next
  case (Array x1)
  then show ?case
  proof (induction cd2)
    case (Value x2)
    show ?case apply (auto)
    proof -
      have "alookup [] (adata.Array x1) \<noteq> alookup [] (adata.Value x2)" by simp
      then show "\<exists>xs. alookup xs (adata.Array x1) \<noteq> alookup xs (adata.Value x2)" by blast
    qed
  next
    case (Array x2)
    show ?case apply (auto)
    proof -
      assume "\<forall>xs. alookup xs (adata.Array x1) = alookup xs (adata.Array x2)"
      then show "x1 = x2"
      proof (rule contrapos_pp)
        assume "x1 \<noteq> x2"
        then have "alookup [] (adata.Array x1) \<noteq> alookup [] (adata.Array x2)" by simp
        then show "\<not> (\<forall>xs. alookup xs (adata.Array x1) = alookup xs (adata.Array x2))" by blast
      qed
    qed
  qed
qed

section \<open>Array Lookup and Memory Copy\<close>

lemma read_alookup_obtains:
  assumes "aread_safe s m l = Some cd"
      and "mlookup m xs l = Some l'"
  shows "\<exists>cd'. aread_safe s m l' = Some cd' \<and> alookup xs cd = Some cd'"
  using assms
proof (induction xs arbitrary: l cd)
  case Nil
  then show ?case
    using alookup.simps(1) mlookup_obtain_empty by blast
next
  case (Cons a xs)
  from Cons(3) obtain xs' l'' 
    where *: "m$l = Some (mdata.Array xs')"
      and x1: "(to_nat a) \<bind> ($) xs'  = Some l''" and **: "mlookup m xs l'' = Some l'"
    using mlookup_obtain_nempty1[OF Cons(3)] apply auto
    apply (case_tac xs)
    using marray_lookup_obtain_single marray_lookup_obtain_multi
    apply (auto simp add:case_memory_def split:option.split_asm mdata.split_asm)
    apply (case_tac "to_nat a") apply auto
    apply (case_tac "x2a $ aaa") by auto

  from Cons(2) *
    have *: "Some cd = those (map (aread_safe (finsert l s) m) xs') \<bind> Some \<circ> adata.Array"  
    using a_data.read_safe_cases[of s m l cd] by fastforce
  then obtain xs''
    where xx1:"those (map (aread_safe (finsert l s) m) xs') = Some xs''" by fastforce
  then have a1: "cd = adata.Array xs''" using * by simp

  moreover obtain cd' where a3: "aread_safe s m l'' = Some cd'"
    by (smt (verit, ccfv_threshold) Option.bind_cong bind.bind_lunit bind_rzero
        a_data.read_safe_subset_same fsubset_finsertI option.discI
        those_map_some_nth x1 xx1)
  moreover have a2: "(to_nat a) \<bind> ($) xs'' = Some cd'"
    by (smt (verit, ccfv_SIG) a3 a_data.read_some_same bind_eq_Some_conv
          local.x1 those_map_nth those_map_some_nth xx1)
  ultimately obtain cd''
    where "aread_safe s m l' = Some cd'' \<and> alookup xs cd' = Some cd''"
    using Cons(1) ** by auto
  moreover have "alookup xs cd' = alookup (a # xs) cd"
    by (simp add: a1 a2)

  ultimately show ?case by simp
qed

lemma mlookup_read_alookup:
  assumes "mlookup m0 is l1 = Some l1'"
    and "aread_safe s m0 l1 = Some cd1"
shows "\<exists>cd'. alookup is cd1 = Some cd'"
  using assms
proof (induction "is"arbitrary:s l1 cd1)
  case Nil
  then show ?case by simp
next
  case (Cons i is')
  then obtain ls i' l'' cd'
    where *: "m0 $ l1 = Some (mdata.Array ls)" 
      and "to_nat i = Some i'"
      and "ls $ i' = Some l''"
      and "mlookup m0 is' l'' = Some l1'"
      and cd'_def: "aread_safe (finsert l1 s) m0 l'' = Some cd'"
    using a_data.mlookup_read_safe_obtain by metis
  then obtain cd''
    where "alookup is' cd' = Some cd''" using Cons(1)[of l''] by blast
  moreover from * obtain cs
    where "cd1 = Array cs"
      and "cs $ i' = Some cd'"
    using a_data.read_safe_array Cons * cd'_def \<open>ls $ i' = Some l''\<close> by blast
  ultimately show ?case using `to_nat i = Some i'` `ls $ i' = Some l''` by auto
qed

section \<open>Array Update\<close>

fun aupdate :: "'v::vtype list \<Rightarrow> 'v adata \<Rightarrow> 'v adata \<Rightarrow> 'v adata option" where
  "aupdate [] v _ = Some v"
| "aupdate (i # is) v (adata.Array xs)
    = to_nat i
    \<bind> (\<lambda>i. (xs $ i \<bind> aupdate is v)
    \<bind> Some \<circ> adata.Array \<circ> list_update xs i)"
| "aupdate _ _ _ = None"

lemma aupdate_obtain:
  assumes "aupdate is v cd = Some cd'"
  obtains
    (nil) "is = []" and "cd' = v"
  | (cons) i is' xs i' i'' cd''
  where "is = i # is'"
    and "cd=adata.Array xs"
    and "to_nat i = Some i'"
    and "xs $ i' = Some i''"
    and "aupdate is' v i'' = Some cd''"
    and "cd' = adata.Array (list_update xs i' cd'')"
  using assms
  apply (cases "is", auto)
  apply (cases cd, auto)
  apply (case_tac " vtype_class.to_nat a", auto)
  apply (case_tac "x2 $ aa", auto)
  apply (case_tac " aupdate list v ab")
  by auto

lemma aupdate_nth_same:
  assumes "aupdate (i # is) v (adata.Array as) = Some (adata.Array as')"
      and "to_nat i = Some i'"
      and "i'' \<noteq> i'"
    shows "as ! i'' = as' ! i''"
  using assms
  apply (cases "as $ i'",auto)
  by (case_tac "aupdate is v a",auto)

lemma aupdate_alookup:
  assumes "aupdate is v cd = Some cd'"
    shows "alookup is cd' = Some v"
  using assms
proof (induction "is" arbitrary:cd cd')
  case Nil
  then show ?case by auto
next
  case (Cons i "is'")
  then obtain xs i' i'' cd''
  where "cd=adata.Array xs"
    and "to_nat i = Some i'"
    and "xs $ i' = Some i''"
    and *: "aupdate is' v i'' = Some cd''"
    and "cd' = adata.Array (list_update xs i' cd'')"
    using aupdate_obtain[of "i # is'" v cd cd']
    by blast
  moreover from * have "alookup is' cd'' = Some v" using Cons.IH by blast
  ultimately show ?case by (auto simp add: nth_safe_def split:if_split_asm)
qed

lemma alookup_aupdate_alookup:
  assumes "alookup xs0 cd0 = Some cd0'"
      and "aupdate xs1 cd0' cd1 = Some cd1'"
    shows "alookup (xs1@ys) cd1' = alookup (xs0@ys) cd0"
  using assms
  by (simp add: alookup_append aupdate_alookup)

lemma alookup_update_some:
  assumes "alookup xs2 cd2 = Some cd"
      and "alookup xs1 cd1 = Some cd"
    shows "alookup xs2 cd2 \<bind> (\<lambda>cd. aupdate xs1 cd cd1) = Some cd1"
proof -
  from assms
  have "aupdate xs1 cd cd1 = Some cd1"
  proof (induction rule:aupdate.induct)
    case (1 v uu)
    then show ?case by auto
  next
    case (2 i "is" v xs)
    then show ?case
    apply (case_tac "vtype_class.to_nat i", auto)
    apply (case_tac "xs $ a", auto)
    by (metis list_update_same_conv nth_safe_def option.distinct(1) option.inject)
  next
    case (3 v va uw vb)
    then show ?case by auto
  qed
  then show ?thesis using assms by simp
qed

lemma alookup_to_nat_same:
assumes "map to_nat xs = map to_nat ys"
  shows "alookup xs cd = alookup ys cd"
  using assms
proof (induction xs arbitrary:ys cd)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then obtain y ys' where "ys = y # ys'" by auto
  show ?case
  proof (cases cd)
    case (Value x1)
    then show ?thesis
      by (simp add: \<open>ys = y # ys'\<close>)
  next
    case (Array xs')
    then show ?thesis
    proof (cases "to_nat a")
      case None
      then have "to_nat y = None" using Cons(2) \<open>ys = y # ys'\<close> by simp
      then show ?thesis using \<open>ys = y # ys'\<close> None Array by simp
    next
      case (Some a')
      then have "to_nat y = Some a'"
        using Cons(2) \<open>ys = y # ys'\<close> by simp
      show ?thesis
      proof (cases "xs' $ a'")
        case None
        then show ?thesis using Some Array \<open>ys = y # ys'\<close> \<open>to_nat y = Some a'\<close>
          by (auto simp add:nth_safe_def split:if_split_asm)
      next
        case s: (Some a'')
        then have "alookup xs a'' = alookup ys' a''" using Cons(1) Cons(2)
          by (simp add: \<open>ys = y # ys'\<close>)
        then show ?thesis using Array Some s \<open>to_nat y = Some a'\<close> \<open>ys = y # ys'\<close>
          by (metis bind.bind_lunit alookup.simps(2))
      qed
    qed
  qed
qed

lemma aupdate_alookup_prefix:
  assumes "ys = xs' @ zs"
      and "map to_nat xs = map to_nat xs'"
      and "aupdate xs v cd = Some cd'"
    shows "alookup ys cd' = alookup zs v"
  using assms
  by (metis bind.bind_lunit alookup_append alookup_to_nat_same aupdate_alookup)

lemma aupdate_alookup_nprefix1:
  assumes "xs = ys @ zs"
      and "aupdate xs v cd = Some cd'"
    shows "alookup ys cd' = alookup ys cd \<bind> aupdate zs v"
  using assms
proof (induction "xs" arbitrary:cd cd' ys)
  case Nil
  then show ?case by auto
next
  case (Cons i "is'")
  show ?case
  proof (cases ys)
    case Nil
    then show ?thesis
      using Cons.prems(1,2) by auto
  next
    case c: (Cons a list)
    moreover from Cons obtain xs i' i'' cd''
    where 1: "cd=adata.Array xs"
      and 2: "to_nat i = Some i'"
      and 3: "xs $ i' = Some i''"
      and 4: "aupdate is' v i'' = Some cd''"
      and 5: "cd' = adata.Array (list_update xs i' cd'')"
      using aupdate_obtain[of "i # is'" v cd cd']
      by blast
    moreover have "is' = list @ zs"
      using Cons.prems(1) c by auto
    ultimately have "alookup list cd'' = alookup list i'' \<bind> aupdate zs v" using Cons.IH[of "list", of i'' cd''] by blast
    moreover have "a = i"
      using Cons.prems(1) c by auto
    ultimately show ?thesis using c 1 2 3 5 by (auto simp add: nth_safe_def) 
  qed
qed

lemma aupdate_alookup_nprefix2:
  assumes "xs = ys' @ zs"
      and "map to_nat ys = map to_nat ys'"
      and "aupdate xs v cd = Some cd'"
    shows "alookup ys cd' = alookup ys cd \<bind> aupdate zs v"
  using assms
  by (metis alookup_to_nat_same aupdate_alookup_nprefix1)

lemma updateCalldata_clookup_nprefix:
  assumes "aupdate (x#xs) v cd = Some cd'"
      and "to_nat x \<noteq> to_nat y"
    shows "alookup (y#zs) cd' = alookup (y#zs) cd"
  using assms
proof (cases rule: aupdate_obtain)
  case nil
  then show ?thesis by auto
next
  case (cons i is' xs i' i'' cd'')
  with assms show ?thesis by (cases "vtype_class.to_nat y", auto simp add:nth_safe_def)
qed

lemma aupdate_alookup_nprefix3:
  assumes "\<nexists>xs'. map to_nat ys = map to_nat xs @ xs'"
      and "\<nexists>ys'. map to_nat xs = map to_nat ys @ ys'"
      and "aupdate xs v cd = Some cd'"
    shows "alookup ys cd' = alookup ys cd"
  using assms
proof (induction "xs" arbitrary:ys cd cd')
  case Nil
  then show ?case
    by (simp add: prefix_def)
next
  case (Cons i "is'")
  then obtain xs i' i'' cd''
  where 1: "cd=adata.Array xs"
    and 2: "to_nat i = Some i'"
    and 3: "xs $ i' = Some i''"
    and 4: "aupdate is' v i'' = Some cd''"
    and 5: "cd' = adata.Array (list_update xs i' cd'')"
    using aupdate_obtain[of "i # is'" v cd cd']
    by blast
  
  from Cons have "ys \<noteq> []" by blast
  then obtain y ys' where "ys = y # ys'" by (meson list.exhaust)
  with Cons(2,3) have "\<not> prefix is' ys' \<and> \<not> prefix ys' is' \<and> to_nat i = to_nat y \<or> to_nat i \<noteq> to_nat y" unfolding prefix_def by auto
  then consider "\<not> prefix is' ys' \<and> \<not> prefix ys' is' \<and> to_nat i = to_nat y" | "to_nat i \<noteq> to_nat y" by blast
  then show ?case
  proof cases
    case *: 1
    then have " \<nexists>xs'. map vtype_class.to_nat ys' = map vtype_class.to_nat is' @ xs' " using Cons(2) \<open>ys = y # ys'\<close>
      by force
    moreover have "\<nexists>xs'. map vtype_class.to_nat is' = map vtype_class.to_nat ys' @ xs' " using Cons(3) \<open>ys = y # ys'\<close>
      using "*" by fastforce
    ultimately have "alookup ys' cd'' = alookup ys' i''" using Cons.IH[OF _ _ 4] by blast
    then show ?thesis using \<open>ys = y # ys'\<close> 1 2 3 5 * by (auto simp add: nth_safe_def)
  next
    case 2
    then show ?thesis using updateCalldata_clookup_nprefix[OF Cons(4), of y] \<open>ys = y # ys'\<close> by blast
  qed
qed

lemma alookup_aupdate_some:
  assumes "\<exists>x. alookup xs cd = Some x"
    shows "\<exists>x. aupdate xs v cd = Some x"
  using assms
proof (induction xs arbitrary:cd)
  case Nil
  then show ?case by simp
next
  case (Cons i is')
  then obtain cd' i' xs x
    where "cd = adata.Array xs"
      and "vtype_class.to_nat i = Some i'"
      and "xs $ i' = Some cd'"
      and *: "alookup is' cd' = Some x"
    using alookup_obtains_some Cons(2) by blast
  moreover from * obtain x'' where "aupdate is' v cd' = Some x''" using Cons(1) by blast
  ultimately show ?case by simp
qed

section \<open>Calldata Update and Memory Copy\<close>

lemma separate_memory:
  assumes "mlookup m xs1 l1 = Some l1'"
  and  "mlookup m xs2 l2 = Some l2'"
  and "m $ l1' = m $ l2'"
  and "aread_safe s1 m l1 = Some cd1"
  and "aread_safe s2 m l2 = Some cd2"
shows "alookup xs2 cd2 \<bind> (\<lambda>cd. aupdate xs1 cd cd1) = Some cd1"
proof -
  from assms obtain cd1' cd2'
    where *: "aread_safe s1 m l1' = Some cd1'" and "alookup xs1 cd1 = Some cd1'"
      and **: "aread_safe s2 m l2' = Some cd2'" and "alookup xs2 cd2 = Some cd2'"
      using
        read_alookup_obtains[OF assms(4,1)]
        read_alookup_obtains[OF assms(5,2)]
      by blast
  moreover from assms(3) have "cd1' = cd2'" using a_data.read_safe_some_same * ** by blast
  ultimately show ?thesis using alookup_update_some by blast
qed

lemma split_memory:
  assumes "aread_safe s1 m l = Some cd"
      and "mlookup m xs l = Some l'"
    shows "aread_safe s1 m l' \<bind> (\<lambda>cd'. aupdate xs cd' cd) = Some cd"
  using assms read_alookup_obtains separate_memory by fastforce

lemma mlookup_read_update:
  assumes "mlookup m0 is l1 = Some l1'"
      and "aread_safe s m0 l1 = Some cd1"
    shows "\<exists>cd'.
            aupdate is cd cd1 = Some cd' \<and>
              (is \<noteq> [] \<longrightarrow>
                (\<exists>ls. m0 $ l1 = Some (mdata.Array ls)
                \<and> (\<exists>as. cd' = adata.Array as \<and> length as = length ls)))"
  using assms
proof (induction "is"arbitrary:s l1 cd1)
  case Nil
  then show ?case by simp
next
  case (Cons i is')
  then obtain ls i' l'' cd'
    where *: "m0 $ l1 = Some (mdata.Array ls)" 
      and **: "to_nat i = Some i'"
      and "ls $ i' = Some l''"
      and "mlookup m0 is' l'' = Some l1'"
      and cd'_def: "aread_safe (finsert l1 s) m0 l'' = Some cd'"
    using a_data.mlookup_read_safe_obtain by metis

  then obtain cd''
    where "aupdate is' cd cd' = Some cd''" using Cons(1)[of l'' "(finsert l1 s)" cd']
  using \<open>mlookup m0 is' l'' = Some l1'\<close> cd'_def by fastforce
  moreover from * obtain as
    where "cd1 = Array as"
      and "as $ i' = Some cd'"
      and "length as = length ls"
    using a_data.read_safe_array Cons * cd'_def \<open>ls $ i' = Some l''\<close> by blast
  ultimately show ?case using `to_nat i = Some i'` `ls $ i' = Some l''` * by simp
qed

lemma read_safe_lookup_update_value:
  assumes "mlookup m0 is1 l1 = Some l1'"
      and "l1' < length m0"
      and "m1 = m0[l1':=mdata.Value v]"
      and "arange_safe s m0 l1 = Some L1"
      and "arange_safe s m0 l1' = Some L1'"
      and "\<forall>l |\<in>| L1 |-| L1'. m1 $ l = m0 $ l"
      and "aread_safe s m0 l1 = Some cd0"
      and "adisjoint m0 L1"
      and "aread_safe s m1 l1 = Some cd1"
    shows "aupdate is1 (Value v) cd0 = Some cd1"
  using assms
proof (induction is1 arbitrary:l1 cd0 cd1 L1 s)
  case Nil
  then show ?case
    by (simp add:case_memory_def split:if_split_asm)
next
  case (Cons i is1')
  from Cons(2)
  obtain ls
    where ls_def: "m0 $ l1 = Some (mdata.Array ls)"
    by (cases is1',auto simp add:case_memory_def split:option.split_asm mdata.split_asm)
  then have m1_ls: "m1 $ l1 = Some (mdata.Array ls)"
    by (metis Cons.prems(1,4) assms(3) data.range_safe_subs data.noloops length_list_update arange_safe_def
        nth_list_update_neq nth_safe_length nth_safe_some)
  moreover from Cons(5) have "l1 |\<notin>| s" by auto
  ultimately have
    *: "Some cd1 = those (map (aread_safe (finsert l1 s) m1) ls) \<bind> Some \<circ> Array"
    using a_data.read_safe_cases[OF Cons(10)] by fastforce
  moreover obtain as
    where as_def: "aupdate (i # is1') (adata.Value v) cd0 = Some (adata.Array as)"
      and "length as = length ls"
    using mlookup_read_update[OF Cons(2,8)] ls_def by fastforce
  moreover have "\<forall>i < length as. Some (as!i) = (map (aread_safe (finsert l1 s) m1) ls) ! i"
  proof (rule, rule)
    fix i'
    assume "i' < length as"
    then have "i'<length ls" using \<open>length as = length ls\<close> by simp
    then have "(ls ! i') \<in> set ls"
      by simp
    show "Some (as ! i') = map (aread_safe (finsert l1 s) m1) ls ! i'"
    proof (cases "to_nat i = Some i'")
      case True
      from Cons(5) \<open>l1 |\<notin>| s\<close> ls_def have
        "fold
          (\<lambda>x y. y \<bind> (\<lambda>y'. arange_safe (finsert l1 s) m0 x \<bind> (\<lambda>l. Some (l |\<union>| y'))))
          ls
          (Some ({|l1|}))
        = Some L1"
        by (simp add: case_memory_def split:if_split_asm)
      then obtain LL
        where LL_def: "arange_safe (finsert l1 s) m0 (ls ! i') = Some LL"
          and "LL |\<subseteq>| L1"
        using ls_def True \<open>i'<length ls\<close> \<open>l1 |\<notin>| s\<close>
        fold_some_subs[of "arange_safe (finsert l1 s) m0" ls "Some {|l1|}" L1 "ls ! i'"] by auto
      moreover from Cons(2) have range_the: "locations m0 (i # is1') l1 = Some (the (locations m0 (i # is1') l1))"
        by (metis mlookup_locations_some option.sel)
      then obtain LLL
        where LLL_def: "locations m0 is1' (ls ! i') = Some LLL"
          and LLL_L3: "(the (locations m0 (i # is1') l1)) =  finsert l1 LLL"
        using \<open>l1 |\<notin>| s\<close> ls_def locations_obtain True
        by (metis \<open>i' < length ls\<close> mdata.inject(2) nth_safe_some option.sel)
      from Cons(2) have ll_def: "mlookup m0 is1' (ls!i') = Some l1'"
        using \<open>l1 |\<notin>| s\<close> ls_def True
        apply (cases " marray_lookup m0 (i # is1') l1",auto)
        by (metis Cons.prems(1) \<open>i' < length ls\<close> mdata.inject(2) mlookup_obtain_nempty2
             nth_safe_some option.inject)

      from Cons(8) have
        "those (map (aread_safe (finsert l1 s) m0) ls) \<bind> Some \<circ> adata.Array = Some cd0"
        using \<open>l1 |\<notin>| s\<close> ls_def using True
        by (auto simp add:case_memory_def split:if_split_asm)
      then obtain cd1'
        where cd1'_def: "aread_safe (finsert l1 s) m0 (ls!i') = Some cd1'"
        using \<open>l1 |\<notin>| s\<close> ls_def True \<open>(ls ! i') \<in> set ls\<close> LL_def a_data.range_safe_read_safe
        by blast

      from Cons(10) have
        "those (map (aread_safe (finsert l1 s) m1) ls) \<bind> Some \<circ> adata.Array = Some cd1"
        using \<open>l1 |\<notin>| s\<close> m1_ls True
        by (auto simp add:case_memory_def split:if_split_asm)
      then obtain cd2'
        where cd2'_def: "aread_safe (finsert l1 s) m1 (ls!i') = Some cd2'"
        using those_map_none[of "aread_safe (finsert l1 s) m1" ls] \<open>(ls ! i') \<in> set ls\<close>
        by fastforce
      thm Cons(1)
      moreover have "aupdate is1' (Value v) cd1' = Some cd2'"
      proof (rule Cons(1)[OF
            ll_def
            Cons(3,4)
            LL_def
            _
            _
            cd1'_def
            _
            cd2'_def
            ])
        have "l1 |\<notin>| L1'"
          using Cons.prems(1,4,5) a_data.noloops by blast
        then show "arange_safe (finsert l1 s) m0 l1' = Some L1'" using Cons(6)
          by (smt (verit, best) finsertE fminusD1 fminusD2 a_data.range_safe_nin_same)
      next
        from Cons(7) show "\<forall>l|\<in>|LL |-| L1'. m1 $ l = m0 $ l" using \<open>LL |\<subseteq>| L1\<close> by blast
      next
        from Cons(9) show "adisjoint m0 LL" using \<open>LL |\<subseteq>| L1\<close> by auto
      qed
      then have "(as ! i') = cd2'"
        using as_def cd1'_def ls_def True Cons(8)
        apply (auto simp add:case_memory_def split:if_split_asm)
        apply (cases cd0,auto)
        apply (case_tac "x2 $ i'",auto)
        apply (case_tac " aupdate is1' (adata.Value v) a",auto)
        apply (case_tac "those (map (aread_safe (finsert l1 s) m0) ls)",auto)
        apply (case_tac "m0 $ (ls ! i')",auto)
        apply (case_tac "ab",auto)
        using \<open>i' < length as\<close> aupdate_obtain apply fastforce
        by (metis \<open>i' < length as\<close> cd1'_def length_list_update map_equality_iff
            nth_list_update_eq nth_safe_some option.inject those_some_map)
      moreover have
        "map (aread_safe (finsert l1 s) m1) ls ! i'
        = aread_safe (finsert l1 s) m1 (ls ! i')"
        by (simp add: \<open>i' < length ls\<close>)
      ultimately show ?thesis by simp
    next  
      case False
      then obtain i''
        where "to_nat i = Some i''"
          and "i'' \<noteq> i'"
          and "i'' < length ls"
        using Cons(2) ls_def 
        apply (case_tac "to_nat i",auto)
        apply (cases is1',auto simp add:case_memory_def)
        using mlookup_obtain_nempty2 by fastforce
      moreover from Cons(8) ls_def have
        *: "those (map (aread_safe (finsert l1 s) m0) ls) \<bind> Some \<circ> Array = Some cd0"
        using \<open>l1 |\<notin>| s\<close> by (auto simp add:case_memory_def)
      moreover from * obtain aa
        where aa_def: "those (map (aread_safe (finsert l1 s) m0) ls) = Some aa"
        by (cases "those (map (aread_safe (finsert l1 s) m0) ls)", auto)
      moreover from aa_def have "length aa = length ls" by (metis length_map those_some_map)
      then have "aread_safe (finsert l1 s) m0 (ls ! i') = Some (aa!i')"
        using * those_map_nth[of "aread_safe (finsert l1 s) m0" ls aa i']
          aa_def `i' < length ls`
        by (auto simp add:nth_safe_def split:if_split_asm option.split_asm)
      ultimately have "aread_safe (finsert l1 s) m0 (ls ! i') = Some (as ! i')"
        using aupdate_nth_same[of i is1' "Value v" aa as i'' i'] as_def by force
      moreover from Cons(5) have
        *:"fold
            (\<lambda>x y. y \<bind> (\<lambda>y'. (arange_safe (finsert l1 s) m0 x) \<bind> (\<lambda>l. Some (l |\<union>| y'))))
            ls
            (Some {|l1|})
        = Some L1" using ls_def
        by (auto simp add:case_memory_def split:if_split_asm)
      then obtain L
        where L_def: "arange_safe (finsert l1 s) m0 (ls ! i') = Some L"
          and "L |\<subseteq>| L1"
        using fold_some_subs[of "arange_safe (finsert l1 s) m0"]
        by (meson \<open>ls ! i' \<in> set ls\<close>)
      moreover have "\<forall>l|\<in>|L. m1 $ l = m0 $ l"
      proof -
        from L_def have "arange m0 (ls ! i') = Some L"
          unfolding arange_def arange_safe_def data.range_def
          using data.range_safe_subset_same by blast
        moreover have "ls ! i'' \<in> set ls" by (simp add: \<open>i'' < length ls\<close>)
        with * have "\<exists>L'. arange_safe (finsert l1 s) m0 (ls ! i'') = Some L'"
          using fold_some_subs[of "arange_safe (finsert l1 s) m0"]
        by (meson) 
        then obtain L' where L'_def: "arange_safe s m0 (ls ! i'') = Some L'"
          using a_data.range_safe_subset_same by blast
        then have "arange m0 (ls ! i'') = Some L'"
          unfolding arange_def arange_safe_def data.range_def
          using data.range_safe_subset_same by blast
        moreover from \<open>ls ! i' \<in> set ls\<close> have "ls $ i' = Some (ls ! i')"
          unfolding nth_safe_def using \<open>i' < length ls\<close> by simp
        moreover have "ls $ i'' = Some (ls ! i'')"
          unfolding nth_safe_def by (simp add: \<open>i'' < length ls\<close>)
        moreover have "l1 |\<in>| L1"
          using Cons.prems(4) a_data.range_safe_subs by auto
        ultimately have "(L |\<inter>| L' = {||})"
          using Cons(9) unfolding a_data.disjoint_def
          using ls_def `i'' \<noteq> i'` by blast
        moreover have "mlookup m0 is1' (ls ! i'') = Some l1'"
          using Cons(2) ls_def \<open>to_nat i = Some i''\<close>
          using \<open>ls $ i'' = Some (ls ! i'')\<close> mlookup_obtain_nempty2 by fastforce
        then have "L1' |\<subseteq>| L'" using a_data.mlookup_range_safe_subs[OF _ Cons(6) L'_def] L'_def by simp
        ultimately have "L |\<inter>| L1' = {||}" by blast
        then show ?thesis using `L |\<subseteq>| L1` Cons(7) by auto
      qed
      ultimately have "aread_safe (finsert l1 s) m1 (ls ! i') = Some (as ! i')"
        using a_data.read_safe_range_safe[of "finsert l1 s" m0 "ls!i'" _ L m1] by blast
      then show ?thesis using \<open>i' < length ls\<close> by auto
    qed
  qed
  ultimately show ?case by (simp add:map_some_those_some)
qed

lemma read_safe_lookup_update:
  assumes "mlookup m0 is1 l1 = Some l1'"
      and "mlookup m0 is2 l2 = Some l2'"
      and "m1 $ l1' = m0 $ l2'"
      and "arange_safe s m0 l1 = Some L1"
      and "arange_safe s m0 l1' = Some L1'"
      and "arange_safe s2 m0 l2 = Some L2"
      and "(\<forall>l |\<in>| L1 |-| L1'. m1 $ l = m0 $ l)"
      and "(\<forall>l |\<in>| L2. m1 $ l = m0 $ l)"
      and "aread_safe s m0 l1 = Some cd1"
      and "aread_safe s2 m0 l2 = Some cd2"
      and "adisjoint m0 L1"
      and "aread_safe s m1 l1 = Some cd"
    shows "alookup is2 cd2 \<bind> (\<lambda>cd. aupdate is1 cd cd1) = Some cd"
  using assms
proof (induction is1 arbitrary:l1 cd cd1 L1 s)
  case Nil
  moreover have "mlookup m1 is2 l2 = Some l2'"
  proof -
    from Nil have "l2' |\<in>| L2" using a_data.range_safe_mlookup by blast
    then have "m1 $ l2' = m0 $ l2'" using Nil(8) by simp
    moreover from Nil(2) obtain L where "locations m0 is2 l2 = Some L"
      using mlookup_locations_some by blast
    then have "L |\<subseteq>| L2" using a_data.range_safe_locations[OF Nil(6)] by simp
    then have "\<forall>l|\<in>|L. m1 $ l = m0 $ l" using Nil(8) by blast
    ultimately show ?thesis
      using mlookup_same_locations[OF Nil(2) `locations m0 is2 l2 = Some L`] by auto
  qed
  moreover from Nil have "m1$l1 = m0$l2'" by simp
  then have "m1$l2' = m1$l1" using Nil a_data.range_safe_mlookup by metis
  then have "m1 $ l1' = m1 $ l2'" by (metis bind.bind_lunit calculation(1) mlookup.simps(1))
  moreover have "aread_safe s2 m1 l2 = Some cd2"
    using a_data.read_safe_range_safe[OF Nil(10,6,8)] .
  ultimately show ?case using separate_memory[of m1 "[]" l1 l1' is2 l2 l2' s cd s2 cd2] by auto
next
  case (Cons i is1')
  from Cons(2)
  obtain ls
    where ls_def: "m0 $ l1 = Some (mdata.Array ls)"
    by (cases is1',auto simp add:case_memory_def split:option.split_asm mdata.split_asm)
  then have m1_ls: "m1 $ l1 = Some (mdata.Array ls)"
    by (metis Cons.prems(1,4,7) assms(5) a_data.range_safe_subs fminus_iff a_data.noloops
        a_data.range_safe_in_subs)
  moreover from Cons(13) have "l1 |\<notin>| s" by auto
  ultimately have
    *: "Some cd = those (map (aread_safe (finsert l1 s) m1) ls) \<bind> Some \<circ> Array"
    using a_data.read_safe_cases[OF Cons(13)] by fastforce
  moreover obtain as
    where as_def: "alookup is2 cd2
            \<bind> (\<lambda>cd. aupdate (i # is1') cd cd1) = Some (adata.Array as)"
      and "length as = length ls"
  proof -
    from Cons(3,11) obtain cd'
      where "alookup is2 cd2 = Some cd'"
      using mlookup_read_alookup by blast
    moreover obtain as
      where "aupdate (i # is1') cd' cd1 = Some (adata.Array as)"
        and "length as = length ls"
      using mlookup_read_update[OF Cons(2,10)] ls_def by fastforce
    ultimately show ?thesis using that by simp
  qed
  moreover have "\<forall>i < length as. Some (as!i) = (map (aread_safe (finsert l1 s) m1) ls) ! i"
  proof (rule, rule)
    fix i'
    assume "i' < length as"
    then have "i'<length ls" using \<open>length as = length ls\<close> by simp
    then have "(ls ! i') \<in> set ls"
      by simp
    show "Some (as ! i') = map (aread_safe (finsert l1 s) m1) ls ! i'"
    proof (cases "to_nat i = Some i'")
      case True
      from Cons(5) \<open>l1 |\<notin>| s\<close> ls_def have
        "fold
          (\<lambda>x y. y \<bind> (\<lambda>y'. arange_safe (finsert l1 s) m0 x \<bind> (\<lambda>l. Some (l |\<union>| y'))))
          ls
          (Some ({|l1|}))
        = Some L1"
        by (simp add: case_memory_def split:if_split_asm)
      then obtain LL
        where LL_def: "arange_safe (finsert l1 s) m0 (ls ! i') = Some LL"
          and "LL |\<subseteq>| L1"
        using ls_def True \<open>i'<length ls\<close> \<open>l1 |\<notin>| s\<close>
        fold_some_subs[of "arange_safe (finsert l1 s) m0" ls "Some {|l1|}" L1 "ls ! i'"] by auto

      from Cons(2) obtain L3 where L3_def: "locations m0 (i # is1') l1 = Some L3"
        using mlookup_locations_some by blast
      obtain LLL
        where LLL_def: "locations m0 is1' (ls ! i') = Some LLL"
          and LLL_L3: "L3 =  finsert l1 LLL"
        using \<open>l1 |\<notin>| s\<close> ls_def locations_obtain[OF L3_def] True
        by (metis \<open>i' < length ls\<close> mdata.inject(2) nth_safe_some option.sel)
      from Cons(2) have ll_def: "mlookup m0 is1' (ls!i') = Some l1'"
        using \<open>l1 |\<notin>| s\<close> ls_def True
        apply (cases " marray_lookup m0 (i # is1') l1",auto)
        by (metis Cons.prems(1) \<open>i' < length ls\<close> mdata.inject(2) mlookup_obtain_nempty2
             nth_safe_some option.inject)

      from Cons(10) have
        "those (map (aread_safe (finsert l1 s) m0) ls) \<bind> Some \<circ> adata.Array = Some cd1"
        using \<open>l1 |\<notin>| s\<close> ls_def using True
        by (auto simp add:case_memory_def split:if_split_asm)
      then obtain cd1'
        where cd1'_def: "aread_safe (finsert l1 s) m0 (ls!i') = Some cd1'"
        using \<open>l1 |\<notin>| s\<close> ls_def True \<open>(ls ! i') \<in> set ls\<close> LL_def a_data.range_safe_read_safe
        by blast

      from Cons(13) have
        "those (map (aread_safe (finsert l1 s) m1) ls) \<bind> Some \<circ> adata.Array = Some cd"
        using \<open>l1 |\<notin>| s\<close> m1_ls True
        by (auto simp add:case_memory_def split:if_split_asm)
      then obtain cd2'
        where cd2'_def: "aread_safe (finsert l1 s) m1 (ls!i') = Some cd2'"
        using those_map_none[of "aread_safe (finsert l1 s) m1" ls] \<open>(ls ! i') \<in> set ls\<close>
        by fastforce
        
      moreover have "alookup is2 cd2 \<bind> (\<lambda>cd. aupdate is1' cd cd1') = Some cd2'"
      proof (rule Cons(1)[OF
            ll_def
            Cons(3,4)
            LL_def
            _
            Cons(7)
            _
            Cons(9)
            cd1'_def
            Cons(11)
            _
            cd2'_def])
        have "l1 |\<notin>| L1'"
          using Cons.prems(1,4,5) a_data.noloops by blast
        then show "arange_safe (finsert l1 s) m0 l1' = Some L1'" using Cons(6)
          by (smt (verit, best) finsertE fminusD1 fminusD2 a_data.range_safe_nin_same)
      next
        from Cons(8) show "\<forall>l|\<in>|LL |-| L1'. m1 $ l = m0 $ l" using \<open>LL |\<subseteq>| L1\<close> by blast
      next
        from Cons(12) show "adisjoint m0 LL" using \<open>LL |\<subseteq>| L1\<close> by auto
      qed
      then have "(as ! i') = cd2'"
        using as_def cd1'_def ls_def True Cons(10)
        apply (auto simp add:case_memory_def split:if_split_asm)
        apply (cases " alookup is2 cd2",auto)
        apply (cases cd1,auto)
        apply (case_tac "x2 $ i'",auto)
        apply (case_tac " aupdate is1' a aa",auto)
        apply (case_tac "those (map (aread_safe (finsert l1 s) m0) ls)",auto)
        apply (case_tac "m0 $ (ls ! i')",auto)
        apply (case_tac "ac",auto)
        using \<open>i' < length as\<close> aupdate_obtain apply fastforce
        by (metis \<open>i' < length as\<close> cd1'_def length_list_update map_equality_iff
            nth_list_update_eq nth_safe_some option.inject those_some_map)
      moreover have
        "map (aread_safe (finsert l1 s) m1) ls ! i'
        = aread_safe (finsert l1 s) m1 (ls ! i')"
        by (metis L3_def True \<open>m0 $ l1 = Some (mdata.Array ls)\<close>
            locations_obtain mdata.inject(2) nth_map nth_safe_length option.inject)
      ultimately show ?thesis by simp
    next  
      case False
      then obtain i''
        where "to_nat i = Some i''"
          and "i'' \<noteq> i'"
          and "i'' < length ls"
        using Cons(2) ls_def 
        apply (case_tac "to_nat i",auto)
        apply (cases is1',auto simp add:case_memory_def)
        using mlookup_obtain_nempty2 by fastforce
      moreover from Cons(10) ls_def have
        *: "those (map (aread_safe (finsert l1 s) m0) ls) \<bind> Some \<circ> Array = Some cd1"
        using \<open>l1 |\<notin>| s\<close> by (auto simp add:case_memory_def)
      moreover from * obtain aa
        where aa_def: "those (map (aread_safe (finsert l1 s) m0) ls) = Some aa"
        by (cases "those (map (aread_safe (finsert l1 s) m0) ls)", auto)
      moreover from aa_def have "length aa = length ls" by (metis length_map those_some_map)
      then have "aread_safe (finsert l1 s) m0 (ls ! i') = Some (aa!i')"
        using * those_map_nth[of "aread_safe (finsert l1 s) m0" ls aa i']
          aa_def `i' < length ls`
        by (auto simp add:nth_safe_def split:if_split_asm option.split_asm)
      moreover from Cons(3,11) obtain cd'
        where "alookup is2 cd2 = Some cd'"
        using mlookup_read_alookup by blast
      ultimately have "aread_safe (finsert l1 s) m0 (ls ! i') = Some (as ! i')"
        using aupdate_nth_same[of i is1' cd' aa as i'' i'] as_def by force
      moreover from Cons(5) have
        *:"fold
            (\<lambda>x y. y \<bind> (\<lambda>y'. (arange_safe (finsert l1 s) m0 x) \<bind> (\<lambda>l. Some (l |\<union>| y'))))
            ls
            (Some {|l1|})
        = Some L1" using ls_def
        by (auto simp add:case_memory_def split:if_split_asm)
      then obtain L
        where L_def: "arange_safe (finsert l1 s) m0 (ls ! i') = Some L"
          and "L |\<subseteq>| L1"
        using fold_some_subs[of "arange_safe (finsert l1 s) m0"]
        by (meson \<open>ls ! i' \<in> set ls\<close>)
      moreover have "\<forall>l|\<in>|L. m1 $ l = m0 $ l"
      proof -
        from L_def have "arange m0 (ls ! i') = Some L"
          unfolding arange_def arange_safe_def data.range_def
          using data.range_safe_subset_same by blast
        moreover have "ls ! i'' \<in> set ls" by (simp add: \<open>i'' < length ls\<close>)
        with * have "\<exists>L'. arange_safe (finsert l1 s) m0 (ls ! i'') = Some L'"
          using fold_some_subs[of "arange_safe (finsert l1 s) m0"]
        by (meson) 
        then obtain L' where L'_def: "arange_safe s m0 (ls ! i'') = Some L'"
          using a_data.range_safe_subset_same by blast
        then have "arange m0 (ls ! i'') = Some L'"
          unfolding arange_def arange_safe_def data.range_def
          using data.range_safe_subset_same by blast
        moreover from \<open>ls ! i' \<in> set ls\<close> have "ls $ i' = Some (ls ! i')"
          unfolding nth_safe_def using \<open>i' < length ls\<close> by simp
        moreover have "ls $ i'' = Some (ls ! i'')"
          unfolding nth_safe_def by (simp add: \<open>i'' < length ls\<close>)
        moreover have "l1 |\<in>| L1"
          using Cons.prems(4) a_data.range_safe_subs by auto
        ultimately have "(L |\<inter>| L' = {||})"
          using Cons(12) unfolding a_data.disjoint_def
          using ls_def `i'' \<noteq> i'` by blast
        moreover have "mlookup m0 is1' (ls ! i'') = Some l1'"
          using Cons(2) ls_def \<open>to_nat i = Some i''\<close>
          using \<open>ls $ i'' = Some (ls ! i'')\<close> mlookup_obtain_nempty2 by fastforce
        thm Cons(6)
        then have "L1' |\<subseteq>| L'" using a_data.mlookup_range_safe_subs[OF _ Cons(6) L'_def] L'_def by simp
        ultimately have "L |\<inter>| L1' = {||}" by blast
        then show ?thesis using `L |\<subseteq>| L1` Cons(8) by auto
      qed
      ultimately have "aread_safe (finsert l1 s) m1 (ls ! i') = Some (as ! i')"
        using a_data.read_safe_range_safe[of "finsert l1 s" m0 "ls!i'" _ L m1] by blast
      then show ?thesis using \<open>i' < length ls\<close> by auto
    qed
  qed
  ultimately show ?case by (simp add:map_some_those_some)
qed

lemma range_safe_update_some:
  assumes "mlookup m0 is1 l1 = Some l1'"
      and "m1 $ l1' = m0 $ l2'"
      and "arange_safe s m0 l1 = Some L1"
      and "arange_safe s m0 l1' = Some L1'"
      and "arange_safe s2 m0 l2' = Some L2'"
      and "(\<forall>l |\<in>| L1 |-| L1'. m1 $ l = m0 $ l)"
      and "(\<forall>l |\<in>| L2'. m1 $ l = m0 $ l)"
      and "adisjoint m0 L1"
      and "s |\<inter>| L2' = {||}"
      and "the (locations m0 is1 l1) |\<inter>| L2' = {||}"
      and "l1' |\<notin>| L2'"
    shows "\<exists>L. arange_safe s m1 l1 = Some L"
  using assms
proof (induction is1 arbitrary:l1 L1 s)
  case Nil
  then have "l1 = l1'" by auto
  then have "m1 $ l1 = m0 $ l2'" using Nil by simp

  have "l1 |\<notin>| s" using Nil(3) by (simp add:case_memory_def split: if_split_asm)
  have "l2' |\<notin>| s2" using Nil(5) by (simp add:case_memory_def split: if_split_asm)

  show ?case
  proof (cases "m1 $ l1")
    case None
    then show ?thesis
      by (metis \<open>m1 $ l1 = m0 $ l2'\<close> assms(5) mlookup.simps(1) not_None_eq
          a_data.mlookup_range_safe_some)
  next
    case (Some a)
    then show ?thesis
    proof (cases a)
      case (Value v)
      then show ?thesis using \<open>l1 |\<notin>| s\<close> Some by (auto simp add:case_memory_def)
    next
      case (Array xs)
      moreover have "\<forall>x \<in> set xs. arange_safe (finsert l1 s) m1 x  \<noteq> None "
      proof
        fix x
        assume "x \<in> set xs"
        moreover have "fold
          (\<lambda>x y. y \<bind> (\<lambda>y'. (arange_safe (finsert l2' s2) m0 x) \<bind> (\<lambda>l. Some (l |\<union>| y'))))
          xs (Some {|l2'|}) = Some L2'"
        using Nil(5) \<open>l2' |\<notin>| s2\<close> \<open>m1 $ l1 = m0 $ l2'\<close> Some Array
        by (auto simp add:case_memory_def split:option.split_asm)
        ultimately obtain X
          where "arange_safe (finsert l2' s2) m0 x = Some X"
            and "X |\<subseteq>| L2'"
          by (metis Array Some \<open>m1 $ l1 = m0 $ l2'\<close> assms(5) a_data.range_safe_obtains_subset)
        then have "arange_safe (finsert l2' s2) m1 x = Some X"
          using Nil(7) a_data.range_safe_same[of "(finsert l2' s2)" m0 x X m1]
          by blast
        moreover have "\<forall>l |\<in>| (finsert l1 s) - (finsert l2' s2). l |\<notin>| X"
        proof -
          have "l1 |\<notin>| X" using Nil.prems(11) \<open>X |\<subseteq>| L2'\<close> \<open>l1 = l1'\<close> by auto
          then show ?thesis using Nil(9) using \<open>X |\<subseteq>| L2'\<close> by blast
        qed
        ultimately have "arange_safe (finsert l1 s) m1 x = Some X" using a_data.range_safe_nin_same[of "(finsert l2' s2)" m1 x X] by blast
        then show "arange_safe (finsert l1 s) m1 x \<noteq> None" by simp
      qed
      then have "fold
              (\<lambda>x y. y \<bind> (\<lambda>y'. (arange_safe (finsert l1 s) m1 x) \<bind> (\<lambda>l. Some (l |\<union>| y'))))
              xs (Some {|l1|}) \<noteq> None"
      using fold_f_set_some[of _ "arange_safe (finsert l1 s) m1"] by blast
      ultimately show ?thesis using Some \<open>l1 |\<notin>| s\<close> by (auto simp add:case_memory_def)
    qed
  qed
next
  case (Cons i is1)
  have "l1 |\<notin>| s" using Cons(4) by (simp add:case_memory_def split: if_split_asm)
  have "l2' |\<notin>| s2" using Cons(6) by (simp add:case_memory_def split: if_split_asm)

  then show ?case
  proof (cases "m1 $ l1")
    case None
    then show ?thesis
      by (metis Cons.prems(1,3,4,6) fminus_iff mlookup_obtain_nempty2 option.discI a_data.range_safe_subs
          a_data.noloops)
  next
    case (Some a)
    then show ?thesis
    proof (cases a)
      case (Value x1)
      moreover obtain xs where "m0$l1 = Some (mdata.Array xs)"
        using mlookup_obtain_nempty2[OF Cons(2)] by auto
      moreover have "l1 |\<notin>| L1'"
        using Cons.prems(1,3,4) a_data.noloops by blast
      ultimately show ?thesis using Cons(7)
        by (metis Cons.prems(3) Some fminusI mdata.distinct(1) option.inject a_data.range_safe_subs)
    next
      case (Array xs)
      moreover have "\<forall>x \<in> set xs. arange_safe (finsert l1 s) m1 x \<noteq> None"
      proof
        fix x assume "x \<in> set xs"
        then obtain i' where x_def: "xs $ i' = Some x"
          by (meson set_nth_some)
        have m1_ls: "m0 $ l1 = Some (mdata.Array xs)"
              by (metis Array Cons.prems(1,3,4,6) Some data.range_safe_subs data.noloops fminus_iff arange_safe_def)
        then obtain j' l'' where "to_nat i = Some j'" and l''_def: "xs $ j' = Some l''" and *: "mlookup m0 is1 l'' = Some l1'"
          using mlookup_obtain_nempty2[OF Cons(2)]
          by (metis mdata.inject(2) option.inject)

        obtain L' where L'_def: "arange_safe (finsert l1 s) m0 l'' = Some L'" and "L' |\<subseteq>| L1"
            by (meson Cons.prems(3) \<open>xs $ j' = Some l''\<close> m1_ls nth_in_set a_data.range_safe_obtains_subset)

        from Cons(2) obtain LL where LL_def: "locations m0 (i # is1) l1 = Some LL"
          using mlookup_locations_some by blast
        show "arange_safe (finsert l1 s) m1 x \<noteq> None"
        proof (cases "i' = j'")
          case True
          then have "x = l''"
            using \<open>xs $ i' = Some x\<close> \<open>xs $ j' = Some l''\<close> by auto
          moreover have "l1 |\<notin>| L1'"
            using Cons.prems(1,3,4) a_data.noloops by blast
          with Cons(5) have "arange_safe (finsert l1 s) m0 l1' = Some L1'" using a_data.range_safe_nin_same[of s m0 l1' L1' "finsert l1 s"] by blast
          moreover from Cons(7) have "\<forall>l|\<in>|L' |-| L1'. m1 $ l = m0 $ l" using \<open>L' |\<subseteq>| L1\<close> by blast
          moreover from Cons(9) have "adisjoint m0 L'" using \<open>L' |\<subseteq>| L1\<close> by auto
          moreover from Cons(2,10,11) have "finsert l1 s |\<inter>| L2' = {||}"
          proof -
            from LL_def have "l1 |\<in>| LL" using locations_l_in_L by blast
            then show ?thesis using Cons(10,11) LL_def by auto
          qed
          moreover have "the (locations m0 is1 l'') |\<inter>| L2' = {||}"
          proof -
            from LL_def obtain LLL where "locations m0 is1 l'' = Some LLL"
              using "*" mlookup_locations_some by blast
            moreover have "mlookup m0 [i] l1 = Some l''" using * \<open>to_nat i = Some j'\<close> l''_def m1_ls by (auto simp add:case_memory_def)
            ultimately have "LLL |\<subseteq>| LL" using mlookup_locations_subs[of m0 "[i]"] LL_def by auto
            then show ?thesis using Cons(11) LL_def \<open>locations m0 is1 l'' = Some LLL\<close> by auto
          qed
          ultimately show ?thesis using Cons(1)[OF * Cons(3) L'_def _ Cons(6) _ Cons(8) _ _ _ Cons(12)] by blast
        next
          case False
          moreover have "l1 |\<in>|L1"
            using Cons.prems(3) a_data.range_safe_subs by auto
          moreover obtain L where L_def: "arange_safe (finsert l1 s) m0 x = Some L" and "L |\<subseteq>| L1" using Cons(4) Some m1_ls \<open>l1 |\<notin>| s\<close>
            by (metis \<open>x \<in> set xs\<close> data.range_safe_obtains_subset arange_safe_def)
          then have "arange m0 x = Some L" unfolding a_data.range_def
            using a_data.range_safe_subset_same by blast
          moreover have "L1' |\<subseteq>| L'" using Cons(5) L'_def a_data.mlookup_range_safe_subs[OF *, of s _ "(finsert l1 s)"] by blast
          moreover from L'_def have "arange m0 l'' = Some L'" unfolding a_data.range_def
            using a_data.range_safe_subset_same by blast
          ultimately have "L |\<inter>| L1' = {||}" using Cons(9) unfolding a_data.disjoint_def using m1_ls x_def l''_def by blast
          then show ?thesis using \<open>L |\<subseteq>| L1\<close> Cons(7) a_data.range_safe_same[of "finsert l1 s" m0 x L m1]
            L_def by blast
        qed
      qed
      then have "fold
              (\<lambda>x y. y \<bind> (\<lambda>y'. (arange_safe (finsert l1 s) m1 x) \<bind> (\<lambda>l. Some (l |\<union>| y'))))
              xs (Some {|l1|}) \<noteq> None"
      using fold_f_set_some[of _ "arange_safe (finsert l1 s) m1"] by blast
      ultimately show ?thesis using Some \<open>l1 |\<notin>| s\<close> by (auto simp add:case_memory_def)
    qed
  qed
qed

lemma range_update_some:
  assumes "mlookup m0 is1 l1 = Some l1'"
      and "m1 $ l1' = m0 $ l2'"
      and "arange m0 l1 = Some L1"
      and "arange m0 l1' = Some L1'"
      and "arange m0 l2' = Some L2'"
      and "(\<forall>l |\<in>| L1 |-| L1'. m1 $ l = m0 $ l)"
      and "(\<forall>l |\<in>| L2'. m1 $ l = m0 $ l)"
      and "adisjoint m0 L1"
      and "the (locations m0 is1 l1) |\<inter>| L2' = {||}"
      and "l1' |\<notin>| L2'"
    shows "\<exists>L. arange m1 l1 = Some L"
  using assms unfolding a_data.range_def
  using range_safe_update_some by blast

lemma range_safe_update_subs:
  assumes "mlookup m0 is1 l1 = Some l1'"
      and "m1 $ l1' = m0 $ l2'"
      and "arange_safe s m0 l1 = Some L1"
      and "arange_safe s m0 l1' = Some L1'"
      and "arange_safe s2 m0 l2' = Some L2'"
      and "(\<forall>l |\<in>| L1 |-| L1'. m1 $ l = m0 $ l)"
      and "(\<forall>l |\<in>| L2'. m1 $ l = m0 $ l)"
      and "adisjoint m0 L1"
      and "arange_safe s m1 l1 = Some L"
    shows "L |\<subseteq>| L1 |\<union>| L2'"
  using assms
proof (induction is1 arbitrary:l1 L L1 s)
  case Nil
  then have "l1 = l1'" by auto
  then have "m1 $ l1 = m0 $ l2'" using Nil by simp

  have "l1 |\<notin>| s" using Nil(3) by (simp add:case_memory_def split: if_split_asm)
  have "l2' |\<notin>| s2" using Nil(5) by (simp add:case_memory_def split: if_split_asm)

  show ?case
  proof (cases "m1 $ l1")
    case None
    then show ?thesis
      by (metis Nil.prems(9) data.range_safe_obtains arange_safe_def option.distinct(1))
  next
    case (Some a)
    then show ?thesis
    proof (cases a)
      case (Value v)
      then have "L = {|l1|}" using Nil(9) \<open>l1 |\<notin>| s\<close> Some by (auto simp add:case_memory_def)
      moreover have "l1 |\<in>| L1" using Nil(3) using a_data.range_safe_subs[of s m0 l1 L1] by simp
      ultimately show ?thesis by simp
    next
      case (Array xs)
      show ?thesis
      proof
        fix x assume "x |\<in>| L"
        moreover have "fold
              (\<lambda>x y. y \<bind> (\<lambda>y'. (arange_safe (finsert l1 s) m1 x) \<bind> (\<lambda>l. Some (l |\<union>| y'))))
              xs (Some {|l1|}) = Some L"
          using Nil(9) using \<open>l1 |\<notin>| s\<close> Some Array by (auto simp add:case_memory_def)
        ultimately consider
          (1) "x = l1"
        | (2) n L'' where "n < length xs \<and> arange_safe (finsert l1 s) m1 (xs ! n) = Some L'' \<and> x |\<in>| L''"
          using fold_union_in[of "arange_safe (finsert l1 s) m1"] by blast
        then show "x |\<in>| L1 |\<union>| L2'"
        proof cases
          case 1
          moreover have "l1 |\<in>| L1" using Nil(3) using a_data.range_safe_subs[of s m0 l1 L1] by simp
          ultimately show ?thesis by simp
        next
          case 2
          moreover have "L'' |\<subseteq>| L2'"
          proof -
            have "fold
              (\<lambda>x y. y \<bind> (\<lambda>y'. (arange_safe (finsert l2' s2) m0 x) \<bind> (\<lambda>l. Some (l |\<union>| y'))))
              xs (Some {|l2'|}) = Some L2'"
              using Nil(5) \<open>l2' |\<notin>| s2\<close> \<open>m1 $ l1 = m0 $ l2'\<close> Some Array
              by (auto simp add:case_memory_def split:option.split_asm)
            then obtain X
              where "arange_safe (finsert l2' s2) m0 (xs ! n) = Some X"
                and "X |\<subseteq>| L2'" using fold_some_subs
              by (metis "2" nth_mem)
            then have "arange_safe (finsert l2' s2) m1 (xs ! n) = Some X"
              using Nil(7) a_data.range_safe_same[of "(finsert l2' s2)" m0 "(xs ! n)" X m1]
              by blast
            then have "arange_safe (finsert l1 s) m1 (xs ! n) = Some X"
              using "2" a_data.range_range by blast
            then show ?thesis
              using \<open>X |\<subseteq>| L2'\<close> a_data.range_range "2" by auto
          qed
          ultimately show ?thesis by blast
        qed
      qed
    qed
  qed
next
  case (Cons i is1)
  have "l1 |\<notin>| s" using Cons(4) by (simp add:case_memory_def split: if_split_asm)
  have "l2' |\<notin>| s2" using Cons(6) by (simp add:case_memory_def split: if_split_asm)

  then show ?case
  proof (cases "m1 $ l1")
    case None
    then show ?thesis
      by (metis Cons.prems(9) option.distinct(1) a_data.read_safe_cases a_data.range_safe_read_safe)
  next
    case (Some a)
    then show ?thesis
    proof (cases a)
      case (Value x1)
      moreover obtain xs where "m0$l1 = Some (mdata.Array xs)"
        using mlookup_obtain_nempty2[OF Cons(2)] by auto
      moreover have "l1 |\<in>| L" using Cons(4)
        using Cons.prems(9) a_data.range_safe_subs by auto
      moreover have "l1 |\<notin>| L1'"
        using Cons.prems(1,3,4) a_data.noloops by blast
      ultimately show ?thesis using Cons(7)
        by (metis Cons.prems(3) Some fminusI mdata.distinct(1) option.inject a_data.range_safe_subs)
    next
      case (Array xs)
      then have "fold
              (\<lambda>x y. y \<bind> (\<lambda>y'. (arange_safe (finsert l1 s) m1 x) \<bind> (\<lambda>l. Some (l |\<union>| y'))))
              xs (Some {|l1|}) = Some L"
          using Cons(10) using \<open>l1 |\<notin>| s\<close> Some by (auto simp add:case_memory_def)
      moreover have "\<forall>x \<in> set xs. \<forall>L. arange_safe (finsert l1 s) m1 x = Some L \<longrightarrow> L |\<subseteq>| L1 |\<union>| L2'"
      proof
        fix x assume "x \<in> set xs"
        then obtain i' where "xs $ i' = Some x"
          by (meson set_nth_some)
        have m1_ls: "m0 $ l1 = Some (mdata.Array xs)"
              by (metis Array Cons.prems(1,3,4,6) Some data.range_safe_subs data.noloops fminus_iff arange_safe_def)
        then obtain j' l'' where "to_nat i = Some j'" and "xs $ j' = Some l''" and *: "mlookup m0 is1 l'' = Some l1'"
          using mlookup_obtain_nempty2[OF Cons(2)]
          by (metis mdata.inject(2) option.inject)
        show "\<forall>L. arange_safe (finsert l1 s) m1 x = Some L \<longrightarrow> L |\<subseteq>| L1 |\<union>| L2'"
        proof (cases "i' = j'")
          case True
          then have "x = l''"
            using \<open>xs $ i' = Some x\<close> \<open>xs $ j' = Some l''\<close> by auto
          show ?thesis
          proof (rule allI, rule impI)
            fix L
            assume L_def: "arange_safe (finsert l1 s) m1 x = Some L"
            obtain LL where LL_def: "arange_safe (finsert l1 s) m0 l'' = Some LL" and "LL |\<subseteq>| L1" using Cons(4) *
              by (metis True \<open>x \<in> set xs\<close> \<open>xs $ i' = Some x\<close> \<open>xs $ j' = Some l''\<close> data.range_safe_obtains_subset arange_safe_def m1_ls option.inject)
            moreover have "L |\<subseteq>| LL |\<union>| L2'"
            proof (rule Cons(1)[OF * Cons(3) LL_def _ Cons(6) _ Cons(8)])
              have "l1 |\<notin>| L1'"
                by (metis Cons.prems(1,3,4) data.noloops arange_safe_def)
              with Cons(5) show "arange_safe (finsert l1 s) m0 l1' = Some L1'" using \<open>l1 |\<notin>| L1'\<close>
                by (smt (verit, best) finsertE fminusD1 fminusD2 a_data.range_safe_nin_same)
            next
              from Cons(7) show "\<forall>l|\<in>|LL |-| L1'. m1 $ l = m0 $ l" using \<open>LL |\<subseteq>| L1\<close> by auto
            next
              from Cons(9) show "adisjoint m0 LL"
                using calculation(2) by auto
            next
              from L_def show "arange_safe (finsert l1 s) m1 l'' = Some L" using \<open>x = l''\<close> by simp
            qed
            ultimately show "L |\<subseteq>| L1 |\<union>| L2'" by auto
          qed
        next
          case False
          show ?thesis
          proof (rule allI, rule impI)
            fix L
            assume L_def: "arange_safe (finsert l1 s) m1 x = Some L"
            moreover from Cons(4) have "fold
              (\<lambda>x y. y \<bind> (\<lambda>y'. (arange_safe (finsert l1 s) m0 x) \<bind> (\<lambda>l. Some (l |\<union>| y'))))
              xs (Some {|l1|}) = Some L1" using m1_ls \<open>l1 |\<notin>| s\<close> by (simp add:case_memory_def)
            then obtain L' where L'_def: "arange_safe (finsert l1 s) m0 x = Some L'" and "L' |\<subseteq>| L1"
              by (metis Cons.prems(3) \<open>x \<in> set xs\<close> data.range_safe_obtains_subset arange_safe_def m1_ls)
            moreover have "L = L'"
            proof -
              have "l1|\<in>|L1"
                by (metis Cons.prems(3) data.range_safe_subs arange_safe_def)
              moreover have "arange m0 x = Some L'" using L'_def
                by (metis bot.extremum a_data.range_def a_data.range_safe_subset_same)
              moreover obtain LL where LL_def: "arange_safe (finsert l1 s) m0 l'' = Some LL"
                by (meson Cons.prems(3) \<open>xs $ j' = Some l''\<close> m1_ls nth_in_set a_data.range_safe_obtains_subset)
              then have "L1' |\<subseteq>| LL" using Cons(5) a_data.mlookup_range_safe_subs[OF *, of s _ "(finsert l1 s)"] by blast
              moreover from LL_def have "arange m0 l'' = Some LL"
                by (metis all_not_fin_conv data.range_safe_nin_same fempty_fminus arange_safe_def a_data.range_def)
              ultimately have "L' |\<inter>| L1' = {||}" using Cons(9) unfolding a_data.disjoint_def
                using m1_ls \<open>L' |\<subseteq>| L1\<close> False \<open>xs $ i' = Some x\<close> \<open>xs $ j' = Some l''\<close> by blast
              then have "\<forall>l|\<in>|L'. m1 $ l = m0 $ l" using Cons(7) `L' |\<subseteq>| L1` by auto
              then show ?thesis using a_data.range_safe_same[OF L'_def] using L_def by simp
            qed
            ultimately show "L |\<subseteq>| L1 |\<union>| L2'" by auto
          qed
        qed
      qed
      moreover have "l1 |\<in>| L1" using Cons(4) a_data.range_safe_subs by blast
      ultimately show ?thesis using fold_subs[of xs "arange_safe (finsert l1 s) m1" "fset (L1 |\<union>| L2')"] by fast
    qed
  qed
qed

lemma range_update_subs:
  assumes "mlookup m0 is1 l1 = Some l1'"
      and "m1 $ l1' = m0 $ l2'"
      and "arange m0 l1 = Some L1"
      and "arange m0 l1' = Some L1'"
      and "arange m0 l2' = Some L2'"
      and "(\<forall>l |\<in>| L1 |-| L1'. m1 $ l = m0 $ l)"
      and "(\<forall>l |\<in>| L2'. m1 $ l = m0 $ l)"
      and "adisjoint m0 L1"
      and "arange m1 l1 = Some L"
    shows "L |\<subseteq>| L1 |\<union>| L2'"
  using range_safe_update_subs[OF assms(1,2) _ _ _ assms(6,7,8)] unfolding arange_def
  by (metis assms(3,4,5,9) a_data.range_def)

section \<open>Initialize Memory\<close>

function "write" :: "'v adata \<Rightarrow> 'v memory \<Rightarrow> location \<times> 'v memory" where
  "write (adata.Value x) m = length_append m (mdata.Value x)"
| "write (adata.Array ds) m = (let (ns, m') = fold_map write ds m in (length_append m' (mdata.Array ns)))"
  by pat_completeness auto
termination
  apply (relation "measure (\<lambda>(s,b). size (s))", auto)
  by (meson Suc_n_not_le_n leI size_list_estimation')

lemma write_sprefix: "sprefix m0 (snd (write cd m0))"
proof (induction arbitrary: m0 rule: write.induct)
  case (1 x m)
  then show ?case unfolding sprefix_def by (auto simp add:length_append_def)
next
  case (2 ds m)
  then have "prefix m0 (snd (fold_map write ds m0))"
  proof (induction ds arbitrary: m0)
    case Nil
    then show ?case by (simp add: prefix_def)
  next
    case (Cons a ds')
    then have IH: "\<And>m0. prefix m0 (snd (fold_map write ds' m0))" by simp
    show ?case
    proof (auto split:prod.split)
      fix m0 x1 x2 x1a x2a
      assume *: "fold_map write ds' x2 = (x1a, x2a)"
        and **: "write a m0 = (x1, x2)"

      from IH have "prefix x2 (snd (fold_map write ds' x2))" by simp
      then have "prefix x2 x2a" using * by simp
      moreover from ** have "prefix m0 x2" using Cons.prems[of a m0] sprefix_prefix by simp
      ultimately show "prefix m0 x2a" unfolding prefix_def by auto
    qed
  qed
  then show ?case unfolding sprefix_def prefix_def
    by (auto split:prod.split simp add:length_append_def)
qed

lemma loc_write_take[simp]:
  assumes "i \<le> j"
      and "j < length ds"
    shows "loc (snd (fold_map write (take i ds) m0)) \<subseteq> loc (snd (fold_map write (take j ds) m0))"
  using assms
proof (induction rule: dec_induct)
  case base
  then show ?case by blast
next
  case (step i)
  moreover from step(4)
  have "prefix (snd (fold_map write (take i ds) m0)) (snd (fold_map write (take (Suc i) ds) m0))"
    by (simp add: Suc_lessD assms fold_map_take_snd write_sprefix sprefix_prefix)
  ultimately show ?case unfolding loc_def prefix_def by auto
qed

lemma write_fold_map_sprefix:
  assumes "ds \<noteq> []"
  shows "sprefix m0 (snd (fold_map write ds m0))"
  using assms
proof (induction ds arbitrary: m0)
  case Nil
  then show ?case unfolding sprefix_def by auto
next
  case (Cons a ds)
  show ?case
  proof (cases ds)
    case Nil
    then show ?thesis using write_sprefix[of m0 a] by (auto split:prod.split)
  next
    case *: (Cons a' list)
    then have "sprefix (snd (write a m0)) (snd (fold_map write ds (snd (write a m0))))"
      using Cons by auto
    then show ?thesis using write_sprefix[of m0 a] sprefix_trans by (auto split:prod.split)
  qed 
qed

lemma write_fold_map_mono:
  assumes "prefix ds' ds"
  shows "prefix (snd (fold_map write ds' m0)) (snd (fold_map write ds m0))"
  using assms
proof (induction ds' arbitrary: ds m0)
  case Nil
  then show ?case
  proof (induction ds arbitrary: m0)
    case Nil
    then show ?case unfolding prefix_def by simp
  next
    case (Cons a ds)
    then show ?case unfolding prefix_def apply (auto split:prod.split)
      by (metis append.assoc write_sprefix sndI sprefix_def)
  qed
next
  case (Cons a ds')
  then show ?case
  proof (induction ds arbitrary: m0)
    case Nil
    then show ?case unfolding prefix_def by simp
  next
    case (Cons a ds)
    then show ?case unfolding prefix_def apply (auto split:prod.split)
      by (metis sndI)
  qed
qed

lemma write_fold_map_smono:
  assumes "sprefix ds' ds"
  shows "sprefix (snd (fold_map write ds' m0)) (snd (fold_map write ds m0))"
  using assms
proof (induction ds' arbitrary: ds m0)
  case Nil
  then have "ds \<noteq> []" unfolding sprefix_def by blast
  then show ?case using write_fold_map_sprefix by auto
next
  case (Cons a ds')
  then show ?case
  proof (induction ds arbitrary: m0)
    case Nil
    then show ?case unfolding sprefix_def by simp
  next
    case (Cons a ds)
    then show ?case unfolding sprefix_def apply (auto split:prod.split) by (metis sndI)
  qed
qed

lemma write_prefix_mono:
  assumes "prefix ds' ds"
  shows
    "prefix
      (butlast (snd (write (adata.Array ds') m0)))
      (butlast (snd (write (adata.Array ds) m0)))"
  using assms apply (auto split: prod.split simp add:length_append_def)
  using write_fold_map_mono
  by (metis snd_conv)

lemma write_prefix_smono:
  assumes "sprefix ds' ds"
  shows
    "sprefix
      (butlast (snd (write (adata.Array ds') m0)))
      (butlast (snd (write (adata.Array ds) m0)))"
  using assms apply (auto split: prod.split simp add:length_append_def)
  using write_fold_map_smono by (metis snd_conv)

lemma write_length_inc: "length (snd (write cd m0)) > length m0"
  using write_sprefix[of m0 cd] unfolding sprefix_def by auto

lemma write_Array_take_Suc:
  assumes "n < length ds"
    shows "fst (write (adata.Array (take (Suc n) ds)) m0)
          = length (snd (write (ds ! n) (butlast (snd (write (adata.Array (take n ds)) m0)))))"
  using assms
proof (induction ds arbitrary: m0 n)
  case Nil
  then show ?case by simp
next
  case (Cons a ds)
  show ?case
  proof (cases n)
    case 0
    then show ?thesis by (simp add:length_append_def split:prod.split)
  next
    case (Suc n')
    then have
      "fst (write (adata.Array (take (Suc n') ds)) (snd (write a m0)))
      = length (snd (write (ds ! n') (butlast (snd (write (adata.Array (take n' ds)) (snd (write a m0)))))))"
      using Cons by auto
    then show ?thesis using Suc by (auto simp add:length_append_def split:prod.split)
  qed
qed

lemma butlast_write[simp]:
  "butlast (snd (write (adata.Array ds) m0)) = snd (fold_map write ds m0)"
  by (auto split:prod.split simp add:length_append_def)

lemma write_sprefix_take:
  assumes "n < length ds"
  shows
    "sprefix
      (snd (write (ds!n) (snd (fold_map write (take n ds) m0))))
      (snd (write (Array ds) m0))"
proof -
  from assms have
    "prefix
      (snd (write (ds ! n) (snd (fold_map write (take n ds) m0))))
      (snd (fold_map write ds m0))"
  proof (induction ds arbitrary: m0 n)
    case Nil
    then show ?case by simp
  next
    case (Cons a xs)
     show ?case
    proof (cases n)
      case 0
      then show ?thesis apply (auto split:prod.split)
        by (metis fold_map_prefix write_sprefix snd_eqD sprefix_prefix)
    next
      case (Suc n')
      then have "n' < length xs" using Cons(2) by simp
      then have
        "prefix
          (snd (write (xs ! n') (snd (fold_map write (take n' xs) (snd (write a m0))))))
          (snd (fold_map write xs (snd (write a m0))))"
        using Cons(1)[of "n'" "(snd (write a m0))"] by simp
      moreover have "((a # xs) ! n) = (xs ! n')" using Suc by simp
      moreover have
        "(snd (fold_map write (take n' xs) (snd (write a m0))))
        = (snd (fold_map write (take n (a # xs)) m0))"
        using Suc(1) by (auto split:prod.split)
      moreover have
        "(snd (fold_map write (a # xs) m0)) = (snd (fold_map write xs (snd (write a m0))))"
        by (auto split:prod.split)
      ultimately show ?thesis by simp
    qed
  qed
  then show ?thesis apply (auto simp add:length_append_def split:prod.split)
    by (smt (verit) Nil_is_append_conv append_assoc not_Cons_self2 prefix_def sprefix_def)
qed

lemma write_length_suc: "length (snd (write ds m)) = Suc (fst (write ds m))"
  by (cases ds) (auto simp add:length_append_def split:prod.split)

lemma write_length_suc2:
  assumes "write ds m0 = (l, m)"
  shows "l = length m - 1"
  using assms write_length_suc[of ds m0] by simp

lemma write_fold_map_less:
  assumes "n < length (fst (fold_map write ds m))"
  shows "fst (fold_map write ds m) ! n < fst (write (Array ds) m)"
  using assms
proof -
  have "n < length ds" using assms
    by (simp add: fold_map_length)

  have "fst (fold_map write ds m) ! n = fst (write (ds ! n) (snd (fold_map write (take n ds) m)))"
    using fold_map_take_fst[OF assms] by simp
  also have "Suc (\<dots>) = length (snd (write (ds ! n) (snd (fold_map write (take n ds) m))))"
    by (simp add: write_length_suc)
  also have "\<dots> < length (snd (write (adata.Array ds) m))"
    using write_sprefix_take[OF \<open>n < length ds\<close>, of m] unfolding sprefix_def by auto
  also have "\<dots> = Suc (fst (write (adata.Array ds) m))"
    by (auto split:prod.split simp add: length_append_def)
  finally show ?thesis by blast
qed

lemma write_obtain:
  obtains xs
    where "snd (write (Array ds) m0) $ fst (write (Array ds) m0) = Some (mdata.Array xs)"
      and "length xs = length ds"
      and "\<forall>n < length xs. xs!n < fst (write (Array ds) m0)
          \<and> xs!n = fst (write (ds!n) (snd (fold_map write (take n ds) m0)))
          \<and> prefix (snd (write (ds!n) (snd (fold_map write (take n ds) m0)))) (snd (write (Array ds) m0))"
proof -
  obtain xs m
    where *: "snd (write (Array ds) m0) = m @ [mdata.Array xs]"
      and **: "xs = fst (fold_map write ds m0)"
      and ***: "fst (write (Array ds) m0) = length m"
    apply (auto simp add:length_append_def split:prod.split prod.split)
    by (simp add: case_prod_beta')

  from ** have "\<forall>n < length xs. xs!n < fst (write (Array ds) m0)
    \<and> xs!n = fst (write (ds!n) (snd (fold_map write (take n ds) m0)))
    \<and> prefix (snd (write (ds!n) (snd (fold_map write (take n ds) m0)))) (snd (write (Array ds) m0))"
    using fold_map_take_fst write_fold_map_less unfolding prefix_def
    by (metis fold_map_length write_sprefix_take sprefix_def)
  moreover from ** have "(length xs = length ds)" using Utils.fold_map_length by metis
  moreover from * ***
  have "snd (write (Array ds) m0) $ fst (write (Array ds) m0) = Some (mdata.Array xs)"
    by auto
  ultimately show ?thesis using that by blast
qed

lemma write_array_less:
  assumes "write cd m = (l, m')"
      and "m'$l = Some (mdata.Array xs)"
      and "xs $ i = Some l'"
    shows "l' < l"
  using assms
proof -
  from assms obtain "ds" where 2: "cd = Array ds" by (case_tac cd, auto simp add: length_append_def)
  then have "snd (write (Array ds) m) $ fst (write (Array ds) m) = Some (mdata.Array xs)"
    using assms by auto
  moreover have "i < length xs" using assms unfolding nth_safe_def by (simp split:if_split_asm)
  ultimately show ?thesis using write_obtain[of ds m]
    by (metis "2" assms(1,3) mdata.inject(2) nth_safe_def option.inject split_pairs2)
qed

lemma range_notin_s:
  assumes "n < length ds"
      and "n < length xs"
      and "\<forall>n < length xs.
            xs!n < fst (write (Array ds) m0) \<and>
            xs!n = fst (write (ds!n) (snd (fold_map write (take n ds) m0)))"
      and "\<forall>l\<ge>length m0. l < length (snd (write (adata.Array ds) m0)) \<longrightarrow> l |\<notin>| s"
    shows "\<forall>l\<ge>length (snd (fold_map write (take n ds) m0)).
            l < length (snd (write (ds!n) (snd (fold_map write (take n ds) m0))))
            \<longrightarrow> l |\<notin>| (finsert (fst (write (adata.Array ds) m0)) s)"
proof (rule allI, rule impI, rule impI)
  fix l
  assume *: "length (snd (fold_map write (take n ds) m0)) \<le> l"
    and **: "l < length (snd (write (ds ! n) (snd (fold_map write (take n ds) m0))))"
  from * have "l\<ge>length m0"
    by (meson dual_order.trans fold_map_geq write_length_inc order.strict_implies_order)
  moreover from assms(2) ** have "l < length (snd (write (adata.Array ds) m0))"
    using write_sprefix_take[OF assms(1), of m0] unfolding sprefix_def by fastforce
  moreover have "l \<noteq> fst (write (adata.Array ds) m0)"
  proof -
    from write_length_suc have
      "length (snd (write (ds ! n) (snd (fold_map write (take n ds) m0))))
      = Suc (fst (write (ds ! n) (snd (fold_map write (take n ds) m0))))"
      by auto
    also from assms(3) have "\<dots> \<le> fst (write (adata.Array ds) m0)" using assms(2) by auto
    finally show ?thesis using ** by simp
  qed
  ultimately show "l |\<notin>| finsert (fst (write (adata.Array ds) m0)) s" using assms(4) by simp
qed

lemma length_write_write:
  assumes "n < length ds"
      and "\<forall>l\<ge>length m0. l < length (snd (write (adata.Array ds) m0)) \<longrightarrow> l |\<notin>| s"
      and "xs!n < fst (write (Array ds) m0)"
      and "xs!n = fst (write (ds!n) (snd (fold_map write (take n ds) m0)))"
  shows "\<forall>l\<ge>length (butlast (snd (write (adata.Array (take n ds)) m0))).
         l < length (snd (write (ds ! n) (butlast (snd (write (adata.Array (take n ds)) m0))))) \<longrightarrow>
         l |\<notin>| finsert (fst (write (adata.Array ds) m0)) s"
proof (rule allI, rule impI, rule impI)
  fix l
  assume *: "length (butlast (snd (write (adata.Array (take n ds)) m0))) \<le> l"
     and **: "l < length (snd (write (ds ! n) (butlast (snd (write (adata.Array (take n ds)) m0)))))"
  from * have "l\<ge>length m0"
    by (metis diff_Suc_1 dual_order.trans length_butlast less_Suc_eq_le write_length_inc write_length_suc)
  moreover from ** have "l < length (snd (write (adata.Array ds) m0))"
  proof -
    from ** have "l < length (snd (fold_map write (take (Suc n) ds) m0))"
      using fold_map_take_snd assms(1) by (metis butlast_write)
    then show ?thesis
      by (metis (no_types, lifting) assms(1) dual_order.strict_trans fold_map_take_snd
          write_sprefix_take sprefix_length)
  qed
  ultimately have "l |\<notin>| s" using assms(2) by blast
  moreover have "l \<noteq> fst (write (adata.Array ds) m0)" using assms(3,4)
    by (metis "**" butlast_write write_length_suc not_less_eq)
  ultimately show "l |\<notin>| finsert (fst (write (adata.Array ds) m0)) s" by blast
qed

lemma marray_lookup_write_take:
  assumes "is \<noteq> []"
      and "write (adata.Array ds) m = (l, m')"
      and "m' $ l = Some (mdata.Array ns)"
      and "ns $ i = Some l'"
      and "marray_lookup m'' is l' = Some (lx, nsx, ix)"
      and "prefix m' m''"
    shows "marray_lookup (snd (fold_map write (take (Suc i) ds) m)) is l' = marray_lookup m'' is l'"
  using assms
proof (induction "is" arbitrary: m l m' ns l' m'' ds i rule: list_nonempty_induct)
  case (single i0)

  from single(1,2)
  have 1: "ns!i = fst (write (ds!i) (snd (fold_map write (take i ds) m)))"
   and 2: "prefix (snd (write (ds!i) (snd (fold_map write (take i ds) m)))) (snd (write (Array ds) m))"
  using write_obtain[of ds m] nth_safe_length single.prems(3)
  by (metis fstI mdata.inject(2) option.inject sndI)+

  have
    3: "snd (write (ds!i) (snd (fold_map write (take i ds) m)))
      = snd (fold_map write (take (Suc i) ds) m)"
    by (metis fold_map_take_snd fst_conv mdata.inject(2) write_obtain nth_safe_length
        option.inject single.prems(1,2,3) snd_conv)

  then have "prefix (snd (fold_map write (take (Suc i) ds) m)) m''" using single(5,1) 2 prefix_def
    by (metis append.assoc fst_conv fst_swap swap_simp)

  moreover have "(snd (fold_map write (take (Suc i) ds) m)) $ l' \<noteq> None" using 1 3 single.prems(3)
    by (metis less_Suc_eq write_length_suc nth_safe_def option.distinct(1) option.inject)

  ultimately have "(snd (fold_map write (take (Suc i) ds) m)) $ l' = m'' $ l'"
    using single nth_safe_prefix by fastforce
  then show ?case by (auto simp add:case_memory_def)
next
  case (cons i0 is0)
  from cons(1) obtain i0' is0' where is0_def: "is0 = i0' # is0'" 
    using list.exhaust by auto
  with cons(6) obtain ns1 i1 l1
    where l1: "m'' $ l' = Some (mdata.Array ns1)"
    and l2: "to_nat i0 = Some i1"
    and l3: "ns1 $ i1 = Some l1"
    and l4: "marray_lookup m'' is0 l1 = Some (lx, nsx, ix)"
    using marray_lookup_obtain_multi[of m'' i0 i0' "is0'" l' "(lx, nsx, ix)"] by blast

  from cons have 0: "\<forall>n < length ns. ns!n < fst (write (Array ds) m)
          \<and> ns!n = fst (write (ds!n) (snd (fold_map write (take n ds) m)))
          \<and> prefix (snd (write (ds!n) (snd (fold_map write (take n ds) m)))) (snd (write (Array ds) m))"
    using write_obtain[of ds m]
    by (metis (no_types, lifting) fst_conv mdata.inject(2) option.inject snd_conv)
  with cons have 1: "ns!i = fst (write (ds!i) (snd (fold_map write (take i ds) m)))"
    by (metis nth_safe_length)

  have "fst (write (ds!i) (snd (fold_map write (take i ds) m))) = l'"
    by (metis "1" cons.prems(3) nth_safe_def nth_safe_length option.sel)
  then have
    "snd (write (ds!i) (snd (fold_map write (take i ds) m)))
    $ fst (write (ds!i) (snd (fold_map write (take i ds) m))) = Some (mdata.Array ns1)"
    using l1 cons(7)
    by (smt (verit) "0" cons.prems(1,3) lessI write_length_suc nth_safe_length nth_safe_prefix
        nth_safe_some snd_conv)
  then obtain "ds'" where 2: "ds!i = adata.Array ds'" 
    apply (case_tac "ds!i") by (auto simp add:length_append_def)

  have 3:
    "snd (write (ds ! i) (snd (fold_map write (take i ds) m)))
      $ fst (write (ds ! i) (snd (fold_map write (take i ds) m)))
    = Some (mdata.Array ns1)"
    by (metis (no_types, lifting) "0" "2" cons.prems(1,3,5) l1 write_obtain nth_safe_length
        nth_safe_prefix nth_safe_some option.inject snd_eqD)

  have 4:
    "marray_lookup
      (snd (fold_map write (take (Suc i1) ds') (snd (fold_map write (take i ds) m)))) is0 l1
    = marray_lookup m'' is0 l1"
  proof (rule cons(2)[
        of
        _
        "(snd (fold_map write (take i ds) m))"
        "fst (write (ds!i) (snd (fold_map write (take i ds) m)))"
        "snd (write (ds!i) (snd (fold_map write (take i ds) m)))",
        OF _ _ l3 l4])
    from 1 2 show
      "write (adata.Array ds') (snd (fold_map write (take i ds) m))
      = (fst (write (ds ! i) (snd (fold_map write (take i ds) m))),
        snd (write (ds ! i) (snd (fold_map write (take i ds) m))))"
      by simp
  next
    from 3 show
      "snd (write (ds ! i) (snd (fold_map write (take i ds) m)))
       $ fst (write (ds ! i) (snd (fold_map write (take i ds) m)))
      = Some (mdata.Array ns1)" by simp
  next
    have "prefix (snd (write (ds ! i) (snd (fold_map write (take i ds) m)))) m'" using cons(3) 0
      by (metis cons.prems(3) nth_safe_length snd_conv)
    moreover have "prefix m' m''" using cons(7) by simp
    ultimately show "prefix (snd (write (ds ! i) (snd (fold_map write (take i ds) m)))) m''"
      unfolding prefix_def by auto
  qed

  have "marray_lookup m'' (i0 # is0) l' = marray_lookup m'' is0 l1"
    using l1 l2 l3 is0_def by (auto simp add:case_memory_def)
  also from 4 have
    "\<dots> =
      marray_lookup
        (snd (fold_map write (take (Suc i1) ds') (snd (fold_map write (take i ds) m)))) is0 l1" ..
  also have "\<dots> =  marray_lookup (snd (fold_map write (take (Suc i) ds) m)) (i0 # is0) l'"
  proof -
    have
      "prefix
        (snd (fold_map write (take (Suc i1) ds') (snd (fold_map write (take i ds) m))))
        (snd (fold_map write (take (Suc i) ds) m))"
      by (metis (no_types, lifting) "2" "3" l3 cons.prems(1,2,3) fold_map_take_snd
          fst_conv mdata.inject(2) write_obtain nth_safe_length option.inject snd_conv)
    then have
      "marray_lookup (snd (fold_map write (take (Suc i1) ds') (snd (fold_map write (take i ds) m)))) is0 l1
       =marray_lookup (snd (fold_map write (take (Suc i) ds) m)) is0 l1"
      by (metis calculation cons.prems(4) marray_lookup_prefix)
    moreover have
      "marray_lookup (snd (fold_map write (take (Suc i) ds) m)) is0 l1
       = marray_lookup (snd (fold_map write (take (Suc i) ds) m)) (i0 # is0) l'"
    proof -
      have "(snd (fold_map write (take (Suc i) ds) m)) $ l' = Some (mdata.Array ns1)" using l1
        by (metis "3" cons.prems(1,2,3) fold_map_take_snd fst_conv mdata.inject(2)
            write_obtain nth_safe_length nth_safe_some option.inject snd_conv)
      then show ?thesis using l2 l3 is0_def by (auto simp add: case_memory_def)
    qed
    ultimately show ?thesis by simp
  qed
  finally show ?case by simp
qed

lemma locations_lookup_write_take:
  assumes "write (adata.Array ds) m = (l, m')"
      and "m' $ l = Some (mdata.Array ns)"
      and "ns $ i = Some l'"
      and "locations m'' is l' = Some L"
      and "prefix m' m''"
    shows "locations (snd (fold_map write (take (Suc i) ds) m)) is l' = locations m'' is l'"
  using assms
proof (induction "is" arbitrary: m l m' ns l' m'' ds i L)
  case Nil
  then show ?case by simp
next
  case (Cons i0 "is0")

  from Cons(5) obtain ns1 i1 l1 L'
    where l1: "m'' $ l' = Some (mdata.Array ns1)"
    and l2: "to_nat i0 = Some i1"
    and l3: "ns1 $ i1 = Some l1"
    and l4: "locations m'' is0 l1 = Some L'"
    and l5: "L = (finsert l' L')"
    using locations_obtain[of m'' i0 is0 l' L] by blast

  from Cons have
    0: "\<forall>n < length ns. ns!n < fst (write (Array ds) m)
       \<and> ns!n = fst (write (ds!n) (snd (fold_map write (take n ds) m)))
       \<and> prefix (snd (write (ds!n) (snd (fold_map write (take n ds) m)))) (snd (write (Array ds) m))"
    using write_obtain[of ds m]
    by (metis (no_types, lifting) fst_conv mdata.inject(2) option.inject snd_conv)
  with Cons have 1: "ns!i = fst (write (ds!i) (snd (fold_map write (take i ds) m)))"
    by (metis nth_safe_length)

  have "fst (write (ds!i) (snd (fold_map write (take i ds) m))) = l'"
    by (metis "1" Cons.prems(3) nth_safe_def nth_safe_length option.sel)
  then have
    "snd (write (ds!i) (snd (fold_map write (take i ds) m)))
    $ fst (write (ds!i) (snd (fold_map write (take i ds) m))) = Some (mdata.Array ns1)"
    using l1 Cons
    by (smt (verit) "0" Cons lessI write_length_suc nth_safe_length nth_safe_prefix nth_safe_some
        snd_conv)
  then obtain "ds'" where 2: "ds!i = adata.Array ds'" 
    apply (case_tac "ds!i") by (auto simp add:length_append_def)

  have
    3: "snd (write (ds ! i) (snd (fold_map write (take i ds) m)))
        $ fst (write (ds ! i) (snd (fold_map write (take i ds) m)))
      = Some (mdata.Array ns1)"
    by (metis (no_types, lifting) "0" "2" Cons(2,4,6) l1 write_obtain nth_safe_length
        nth_safe_prefix nth_safe_some option.inject snd_eqD)

  have 4:
    "locations (snd (fold_map write (take (Suc i1) ds') (snd (fold_map write (take i ds) m)))) is0 l1
    = locations m'' is0 l1"
  proof (rule Cons(1)[
      of
      _
      "(snd (fold_map write (take i ds) m))"
      "fst (write (ds!i) (snd (fold_map write (take i ds) m)))"
      "snd (write (ds!i) (snd (fold_map write (take i ds) m)))",
      OF _ _ l3 l4])
    from 1 2 show
      "write (adata.Array ds') (snd (fold_map write (take i ds) m))
      = (fst (write (ds ! i) (snd (fold_map write (take i ds) m))),
        snd (write (ds ! i) (snd (fold_map write (take i ds) m))))"
      by simp
  next
    from 3 show
      "snd (write (ds ! i) (snd (fold_map write (take i ds) m)))
      $ fst (write (ds ! i) (snd (fold_map write (take i ds) m)))
      = Some (mdata.Array ns1)" by simp
  next
    have "prefix (snd (write (ds ! i) (snd (fold_map write (take i ds) m)))) m'" using Cons(3) 0
      by (metis Cons(2,4) nth_safe_length snd_conv)
    moreover have "prefix m' m''" using Cons by simp
    ultimately show "prefix (snd (write (ds ! i) (snd (fold_map write (take i ds) m)))) m''"
      unfolding prefix_def by auto
  qed

  have "locations m'' (i0 # is0) l' = Some (finsert l' (the (locations m'' is0 l1)))"
    using l1 l2 l3 l4 Cons by (auto simp add:case_memory_def)
  also from 4 have
    "locations m'' is0 l1
    = locations (snd (fold_map write (take (Suc i1) ds') (snd (fold_map write (take i ds) m)))) is0 l1" ..
  also have
    "Some (
      finsert
        l'
        (the (locations (snd (fold_map write (take (Suc i1) ds') (snd (fold_map write (take i ds) m)))) is0 l1)))
    = locations (snd (fold_map write (take (Suc i) ds) m)) (i0 # is0) l'"
  proof -
    have
      "prefix
        (snd (fold_map write (take (Suc i1) ds') (snd (fold_map write (take i ds) m))))
        (snd (fold_map write (take (Suc i) ds) m))"
      by (metis "2" "3" Cons.prems(1,2,3) l3 fold_map_take_snd fst_conv mdata.inject(2)
          write_obtain nth_safe_length option.inject snd_conv)
    then have
      "locations (snd (fold_map write (take (Suc i1) ds') (snd (fold_map write (take i ds) m)))) is0 l1
       = locations (snd (fold_map write (take (Suc i) ds) m)) is0 l1"
      by (metis "4" l4 locations_prefix_locations)
    moreover have
      "Some (finsert l' (the (locations (snd (fold_map write (take (Suc i) ds) m)) is0 l1)))
       = locations (snd (fold_map write (take (Suc i) ds) m)) (i0 # is0) l'"
    proof -
      have "(snd (fold_map write (take (Suc i) ds) m)) $ l' = Some (mdata.Array ns1)" using l1
        by (metis "3" Cons(2,3,4) fold_map_take_snd fst_conv mdata.inject(2) write_obtain
            nth_safe_length nth_safe_some option.inject snd_conv)
      then show ?thesis using l2 l3 l4 apply (auto simp add: case_memory_def)
        apply (case_tac "locations (snd (fold_map write (take (Suc i) ds) m)) is0 l1", auto)
        by (metis "4" calculation option.distinct(1))
    qed
    ultimately show ?thesis by simp
  qed
  finally show ?case by simp
qed

section \<open>Memory Init and Lookup\<close>

lemma marray_lookup_write_less:
  assumes "is \<noteq> []"
    and "write cd m = (l, m')"
    and "marray_lookup m' is l = Some (lx, nsx, ix)"
    and "nsx $ ix = Some l'"
  shows "l' < l"
  using assms
proof (induction "is" arbitrary: m l m' cd rule: list_nonempty_induct)
  case (single i0)
  then have "m' $ lx = Some (mdata.Array nsx)" and "to_nat i0 = Some ix" and "lx = l"
    using marray_lookup_obtain_single[OF single(2)] by auto
  then show ?case using single.prems(1,3) write_array_less by blast
next
  case (cons i0 is0)

  from cons(1) obtain i0' is0'
    where is0_def: "is0 = i0' # is0'"
    using list.exhaust by auto
  with cons(4) obtain ns1 i1 l1
    where l1: "m' $ l = Some (mdata.Array ns1)"
    and l2: "to_nat i0 = Some i1"
    and l3: "ns1 $ i1 = Some l1"
    and l4: "marray_lookup m' is0 l1 = Some (lx, nsx, ix)"
  using marray_lookup_obtain_multi[of m' i0 i0' "is0'" l "(lx, nsx, ix)"] by blast

  from cons(3) l1 obtain "ds" where 2: "cd = Array ds" by (case_tac cd, auto simp add: length_append_def)

  have "l1 < l" by (meson cons.prems(1) l1 l3 write_array_less)
  moreover have "l' < l1"

  proof (rule cons(2)[OF _ _ cons(5)])
    from cons have
      0: "\<forall>n < length ns1. ns1!n < fst (write (Array ds) m)
       \<and> ns1!n = fst (write (ds!n) (snd (fold_map write (take n ds) m)))
       \<and> prefix (snd (write (ds!n) (snd (fold_map write (take n ds) m)))) (snd (write (Array ds) m))"
      using write_obtain[of ds m]
      by (smt (verit, ccfv_SIG) "2" l1 mdata.inject(2) option.inject split_pairs2)
    then show
      "write (ds!i1) (snd (fold_map write (take i1 ds) m))
      = (l1, (snd (fold_map write (take (Suc i1) ds) m)))"
      by (metis "2" l1 cons.prems(1) fold_map_take_snd l3 mdata.inject(2) write_obtain
          nth_safe_def nth_safe_length option.inject split_pairs2)
  next
    from l4 show "marray_lookup (snd (fold_map write (take (Suc i1) ds) m)) is0 l1 = Some (lx, nsx, ix)"
      using marray_lookup_write_take[OF cons(1) _ l1 l3 l4 ] cons(3) 2 by auto
  qed
  ultimately show ?case by simp
qed

lemma write_marray_lookup_locations:
  assumes "write cd m = (l, m')"
      and "marray_lookup m' xs l = Some (l1, xs1, i1)"
      and "xs1 $ i1 = Some l2"
      and "locations m' xs l = Some L"
    shows "l2 |\<notin>| L"
  using assms
proof (induction xs arbitrary:L l cd m m')
  case Nil
  then show ?case by simp
next
  case (Cons i xs')
  then show ?case
  proof (cases xs')
    case Nil
    then show ?thesis
    proof (cases cd)
      case (Value x1)
      then show ?thesis
      using Cons(2,3,4) Nil by (auto simp add: length_append_def case_memory_def)
    next
      case (Array ca)
      then obtain ns m''
        where "fold_map write ca m = (ns, m'')"
          and "l = length m''"
          and "m' = m'' @ [mdata.Array ns]"
        using Cons(2,3,4) Nil  apply (case_tac "fold_map write ca m")
        by (auto simp add: length_append_def case_memory_def)
      then have *: "m'$l = Some (mdata.Array ns)" using Cons by simp
      moreover from * obtain i''
        where ***: "to_nat i = Some i''"
          and "(l1, xs1, i1) = (l, ns, i'')"
        using Cons Nil apply (auto simp add: length_append_def case_memory_def)
        by (case_tac " vtype_class.to_nat i") auto
      then have **: "ns$i'' =Some l2" using Cons by simp
      moreover have "locations m' (i # xs') l =Some {|l|}"
        using Cons(5) Nil * ** *** by (auto simp add: length_append_def case_memory_def)
      ultimately show ?thesis using Cons.prems(4) write_array_less Cons(2) by fastforce
    qed
  next
    case c2: (Cons i' is')
    then show ?thesis
    proof (cases cd)
      case (Value x1)
      then show ?thesis
      using Cons(2,3,4) c2 Nil by (auto simp add: length_append_def case_memory_def)
    next
      case (Array ca)
      then obtain ns m''
        where 0: "fold_map write ca m = (ns, m'')"
          and "l = length m''"
          and "m' = m'' @ [mdata.Array ns]"
        using Cons(2,3,4) Nil apply (case_tac "fold_map write ca m")
        by (auto simp add: length_append_def case_memory_def)

      then obtain i'' l'
        where 1: "m' $ l = Some (mdata.Array ns)"
          and 2: "to_nat i = Some i''"
          and 3: "ns $ i'' = Some l'"
          and 4: "marray_lookup m' xs' l' = Some (l1, xs1, i1)"
        using marray_lookup_obtain_multi[of m' i i' is' l "(l1, xs1, i1)"] Cons(3) c2
        by (metis mdata.inject(2) nth_append_length nth_safe_length nth_safe_some option.inject)

      from 1 2 3 4 obtain L'
      where 5:"locations m' (i'#is') l' = Some L'"
        and 6: "L = (finsert l L')"
        using locations_obtain[OF Cons(5)] c2 by force

      have "i'' < length (fst (fold_map write ca m))"
        by (simp add: "3" \<open>fold_map write ca m = (ns, m'')\<close> nth_safe_length)
      then have
        7: "fst (fold_map write ca m) ! i''
        = fst (write (ca ! i'') (snd (fold_map write (take i'' ca) m)))"
        using fold_map_take_fst by metis

      have "i'' < length ca"
        by (metis \<open>i'' < length (fst (fold_map write ca m))\<close> fold_map_length)
      then have
        8: "snd (fold_map write (take (Suc i'') ca) m)
         = snd (write (ca ! i'') (snd (fold_map write (take i'' ca) m)))"
        using fold_map_take_snd by metis

      obtain mx lx
        where 12: "fold_map write (take i'' ca) m = (lx, mx)"
          and 13: "write (ca!i'') mx
              = (fst (fold_map write ca m) ! i'', snd (fold_map write (take (Suc i'') ca) m))"
        using 7 8 by fastforce

      have "(fst (fold_map write ca m) ! i'') = l'"
        by (metis "3" 0 fst_conv nth_safe_length nth_safe_some option.inject)
      then have
        "marray_lookup (snd (fold_map write (take (Suc i'') ca) m)) xs' (fst (fold_map write ca m) ! i'')
        = marray_lookup m' xs' l'"
        using c2 marray_lookup_write_take 1 "2" 3 "4" Array Cons.prems(1,2) `i'' < length ca`
        by blast
      then have
        9: "marray_lookup (snd (fold_map write (take (Suc i'') ca) m)) xs' (fst (fold_map write ca m) ! i'')
          = Some (l1, xs1, i1)" using 4 by simp

      have "fst (fold_map write ca m) ! i'' = l'"
        by (metis "3" \<open>fold_map write ca m = (ns, m'')\<close> fst_conv nth_safe_length nth_safe_some option.inject)
      then have
        "locations (snd (fold_map write (take (Suc i'') ca) m)) xs' (fst (fold_map write ca m) ! i'')
        = locations m' (i'#is') l'"
        using c2 locations_lookup_write_take "1" "3" Array Cons.prems(1) 5 by blast
      then have
        10: "locations (snd (fold_map write (take (Suc i'') ca) m)) xs' (fst (fold_map write ca m) ! i'')
          = Some L'" using 5 by simp

      have "l2 |\<notin>| L'" using Cons(1)[OF 13 9 Cons(4) 10] by simp
      moreover from marray_lookup_write_less have "l2 \<noteq> l"
        using Cons.prems(1,2) assms(3) by blast
      ultimately show ?thesis using 12 13 6 by blast
    qed
  qed
qed

lemma write_lookup_some:
  assumes "xs \<noteq> []"
      and "write cd m = (l, m')"
      and "alookup xs cd = Some x"
      and "prefix m' m''"
    shows "\<exists>lz xsz iz z. marray_lookup m'' xs l = Some (lz, xsz, iz) \<and> xsz $ iz = Some z"
  using assms
proof (induction xs arbitrary: m l m' cd x m'' rule: list_nonempty_induct)
  case (single i0)
  from single(2) obtain ds i
    where "cd = adata.Array ds"
      and l2: "to_nat i0 = Some i"
      and l3: "ds $ i = Some x"
    apply (cases cd,auto)
    apply (cases "to_nat i0",auto)
    by (case_tac "x2$a",auto)
  then show ?case using single.prems(1,3)
    apply (auto simp add:case_memory_def)
    apply (cases "m'' $ l",auto)
    apply (metis fst_conv write_obtain nth_safe_prefix option.distinct(1) single.prems(1,3) snd_conv)
    apply (case_tac a,auto simp add:nth_safe_def length_append_def split:if_split_asm prod.split_asm)
    apply (metis length_append_singleton lessI mdata.distinct(1) nth_append_left nth_append_length prefix_def)
    by (metis fold_map_length fst_eqD length_append_singleton mdata.inject(2) not_less_eq nth_append_left nth_append_length prefix_def verit_comp_simplify1(1))
next
  case (cons i0 is0)

  from cons(4) obtain ds i cd'
    where a1: "cd = adata.Array ds"
      and a2: "to_nat i0 = Some i"
      and a3: "ds $ i = Some cd'"
      and a4: "alookup is0 cd' = Some x"
    apply (cases cd,auto)
    apply (cases "to_nat i0",auto)
    by (case_tac "x2$a",auto)

  then obtain ns
    where b1: "m' $ l = Some (mdata.Array ns)"
      and b2: "length ds = length ns"
      and b3: "\<forall>n < length ns. ns!n < fst (write (Array ds) m)
          \<and> ns!n = fst (write (ds!n) (snd (fold_map write (take n ds) m)))
          \<and> prefix (snd (write (ds!n) (snd (fold_map write (take n ds) m)))) (snd (write (Array ds) m))"
    using write_obtain[of ds m]
    using cons(4)
    by (metis cons.prems(1) fstI write_obtain snd_eqD)
  moreover from a3 have "i < length ds" unfolding nth_safe_def by (simp split:if_split_asm)
  ultimately have *: "ns!i = fst (write (ds!i) (snd (fold_map write (take i ds) m)))"
    by (simp add: \<open>length ds = length ns\<close>)

  have
    "\<exists>lz xsz iz z. marray_lookup m'' is0 (fst (write (ds!i) (snd (fold_map write (take i ds) m))))
    = Some (lz, xsz, iz) \<and> xsz $ iz = Some z"
  proof (rule cons(2)[OF _ a4])
    from * show
      "write cd' (snd (fold_map write (take i ds) m)) =
        (fst (write (ds ! i) (snd (fold_map write (take i ds) m))),
        snd (write (ds ! i) (snd (fold_map write (take i ds) m))))"
      using \<open>i < length ds\<close> a3 by fastforce
  next
    have "prefix (snd (write (ds ! i) (snd (fold_map write (take i ds) m)))) m'"
      by (metis a1 b2 b3 \<open>i < length ds\<close> cons.prems(1) snd_conv)
    then show "prefix (snd (write (ds ! i) (snd (fold_map write (take i ds) m)))) m''"
      using cons(5) prefix_trans by blast
  qed
  then obtain lz xsz iz z
    where
      "marray_lookup m'' is0 (fst (write (ds!i) (snd (fold_map write (take i ds) m))))
      = Some (lz, xsz, iz)"
      and "xsz $ iz = Some z"
    by blast
  moreover from b1 have "m''$l = Some (mdata.Array ns)"
    by (meson cons.prems(3) nth_safe_prefix)
  ultimately show ?case using * a2 b2 \<open>i < length ds\<close>
    by (cases is0,auto simp add:case_memory_def)
qed

lemma mlookup_some:
  assumes "write cd m = (l, m')"
      and "alookup xs cd = Some x"
    shows "\<exists>y. mlookup m' xs l = Some y"
proof (cases xs)
  case Nil
  then show ?thesis by simp
next
  case (Cons a list)
  moreover obtain  lz xsz iz z
    where "marray_lookup m' (a # list) l = Some (lz, xsz, iz)"
      and "xsz $ iz = Some z"
    using write_lookup_some[of "a # list", OF _ assms(1), of x m']
    using assms(2) Cons by blast
  ultimately show ?thesis by simp
qed

lemma write_mlookup_locations:
  assumes "write cd m = (l, m')"
      and "mlookup m' xs l = Some l1"
      and "locations m' xs l = Some L"
    shows "l1 |\<notin>| L"
proof (cases xs)
  case Nil
  then show ?thesis
    using assms(3) by auto
next
  case (Cons a list)
  then obtain l1' xs1 i1 l2
    where "marray_lookup m' xs l = Some (l1', xs1, i1)"
      and "xs1 $ i1 = Some l2"
      and "l1 = l2"
    using mlookup_obtain_nempty1[of m' a list l l1] using assms(2) by metis
  then have "l2 |\<notin>| L" using write_marray_lookup_locations[OF assms(1) _ _ assms(3)] by blast
  then show ?thesis using `l1 = l2` by simp
qed

lemma write_locations_some:
  assumes "write cd m = (l, m')"
      and "alookup xs cd = Some x"
      and "prefix m' m''"
    shows "\<exists>y. locations m'' xs l = Some y"
  using assms
proof (induction xs arbitrary: m l m' cd x m'')
  case Nil
  then show ?case by simp
next
  case (Cons i0 "is")
  from Cons(3) obtain ds i cd'
    where a1: "cd = adata.Array ds"
      and a2: "to_nat i0 = Some i"
      and a3: "ds $ i = Some cd'"
      and a4: "alookup is cd' = Some x"
    apply (cases cd,auto)
    apply (cases "to_nat i0",auto)
    by (case_tac "x2$a",auto)

  then obtain ns
    where b1: "m' $ l = Some (mdata.Array ns)"
      and b2: "length ds = length ns"
      and b3: "\<forall>n < length ns. ns!n < fst (write (Array ds) m)
          \<and> ns!n = fst (write (ds!n) (snd (fold_map write (take n ds) m)))
          \<and> prefix (snd (write (ds!n) (snd (fold_map write (take n ds) m)))) (snd (write (Array ds) m))"
    using write_obtain[of ds m]
    using Cons
    by (metis Cons(2) fstI write_obtain snd_eqD)
  moreover from a3 have "i < length ds" unfolding nth_safe_def by (simp split:if_split_asm)
  ultimately have *: "ns!i = fst (write (ds!i) (snd (fold_map write (take i ds) m)))"
    by (simp add: \<open>length ds = length ns\<close>)

  have "\<exists>y. locations m'' is (fst (write (ds!i) (snd (fold_map write (take i ds) m)))) = Some y"
  proof (rule Cons(1)[OF _ a4])
    from * show
      "write cd' (snd (fold_map write (take i ds) m)) =
        (fst (write (ds ! i) (snd (fold_map write (take i ds) m))),
         snd (write (ds ! i) (snd (fold_map write (take i ds) m))))"
      using \<open>i < length ds\<close> a3 by fastforce
  next
    have "prefix (snd (write (ds ! i) (snd (fold_map write (take i ds) m)))) m'"
      by (metis b2 b3 a1 \<open>i < length ds\<close> Cons.prems(1) snd_conv)
    then show "prefix (snd (write (ds ! i) (snd (fold_map write (take i ds) m)))) m''"
      using Cons prefix_trans by blast
  qed
  then obtain y
    where "locations m'' is (fst (write (ds!i) (snd (fold_map write (take i ds) m)))) = Some y"
    by blast
  moreover from b1 have "m''$l = Some (mdata.Array ns)"
    by (meson Cons nth_safe_prefix)
  ultimately show ?case using * a2 b2 \<open>i < length ds\<close>
    by (cases "is",auto simp add:case_memory_def)
qed

section \<open>Memory Init and Memory Locations\<close>

lemma write_range_safe_in:
  assumes "write (adata.Array ds) m0 = (l, m)"
      and "arange_safe s m l = Some L"
      and "x |\<in>| L"
    shows "x = l \<or>
            (\<exists>n y L'. n<length ds \<and> fst (write (ds ! n) (snd (fold_map write (take n ds) m0)))
            = y \<and> arange_safe s m y = Some L' \<and> x |\<in>| L')"
proof -
  from assms write_obtain[of ds m0] obtain xs
    where *: "m $ l = Some (mdata.Array xs)"
      and "length xs = length ds"
      and **: "\<forall>n<length xs.
              xs ! n < fst (write (adata.Array ds) m0) \<and>
              xs ! n = fst (write (ds ! n) (snd (fold_map write (take n ds) m0)))
                \<and> prefix (snd (write (ds ! n) (snd (fold_map write (take n ds) m0)))) m"
    by auto
  moreover from assms(2) * have
    "fold
      (\<lambda>x y. y \<bind> (\<lambda>y'. (arange_safe (finsert l s) m x) \<bind> (\<lambda>l. Some (l |\<union>| y'))))
      xs
      (Some {|l|})
    = Some L"
    by (auto simp add:case_memory_def split:if_split_asm)
  ultimately have
    "x = l \<or> (\<exists>n L'. n < length xs \<and> arange_safe (finsert l s) m (xs ! n) = Some L' \<and> x |\<in>| L')"
    using fold_union_in[of "arange_safe (finsert l s) m"] assms(3) by blast
  then show ?thesis
  proof
    assume "x = l"
    then show ?thesis by simp
  next
    assume "\<exists>n L'. n < length xs \<and> arange_safe (finsert l s) m (xs ! n) = Some L' \<and> x |\<in>| L'"
    then obtain n L'
      where "n < length xs"
        and ***: "arange_safe (finsert l s) m (xs ! n) = Some L'"
        and "x |\<in>| L'" by blast
    moreover from *** have "arange_safe s m (xs ! n) = Some L'"
      using a_data.range_safe_subset_same by blast
    ultimately show ?thesis using ** by (metis \<open>length xs = length ds\<close>)
  qed
qed

theorem write_arange_safe:
  assumes "\<forall>l \<ge> length m0. l < length (snd (write cd m0)) \<longrightarrow> \<not> l |\<in>| s"
  shows "s_disj_fs (loc m0) (arange_safe s (snd (write cd m0)) (fst (write cd m0)))"
  using assms
proof (induction cd arbitrary: m0 s)
  case (Value x)
  then show ?case
    by (auto simp add: s_disj_fs_def pred_some_def length_append_def case_memory_def loc_def)
next
  case (Array ds)
  from write_obtain obtain xs
    where xs1: "snd (write (Array ds) m0) $ fst (write (Array ds) m0) = Some (mdata.Array xs)"
      and xs2: "length xs = length ds"
      and xs3: "\<forall>n < length xs. xs!n < fst (write (Array ds) m0) \<and>
                                xs!n = fst (write (ds!n) (snd (fold_map write (take n ds) m0)))"
    by metis
  moreover have "\<not> fst (write (Array ds) m0) |\<in>| s" using Array(2)
    by (metis less_Suc_eq_le write_length_inc write_length_suc nth_safe_length xs1)
  ultimately have
    "arange_safe s
        (snd (write (adata.Array ds) m0))
        (fst (write (adata.Array ds) m0))
     = fold (\<lambda>x y.
        y \<bind> (\<lambda>y'. (arange_safe (finsert (fst (write (Array ds) m0)) s) (snd (write (Array ds) m0)) x)
          \<bind> (\<lambda>l. Some (l |\<union>| y'))))
       xs (Some {|fst (write (Array ds) m0)|})" (is "_ = fold ?f xs (Some {|fst (write (Array ds) m0)|})")
    by (simp add:case_memory_def) 
  moreover have "s_disj_fs (loc m0) (fold ?f xs (Some {|fst (write (Array ds) m0)|}))"
  proof (rule take_all1[of xs])
    show "\<forall>n\<le>length xs. s_disj_fs (loc m0) (fold ?f (take n xs) (Some {|fst (write (Array ds) m0)|}))"
    proof (rule allI, rule impI)
      fix n
      assume "n \<le> length xs"
      then show "s_disj_fs (loc m0) (fold ?f (take n xs) (Some {|fst (write (Array ds) m0)|}))"
      proof (induction n)
        case 0
        then show ?case
          using write_fold_map_sprefix[of ds m0, THEN sprefix_length]
          by (fastforce simp add:s_disj_fs_def pred_some_def length_append_def loc_def split:prod.split)
      next
        case (Suc n)
        
        from Suc(2) have "n < length xs" by auto
        then have "n < length ds" using xs2 by simp

        from Suc(2) have
          "fold ?f (take (Suc n) xs) (Some {|fst (write (Array ds) m0)|})
          = ?f (xs!n) (fold ?f (take n xs) (Some {|fst (write (Array ds) m0)|}))"
          by (simp add: fold_take)
        moreover have "s_disj_fs (loc m0) (fold ?f (take n xs) (Some {|fst (write (Array ds) m0)|}))"
          using Suc by simp
        moreover have "\<And>s. s_disj_fs (loc m0) s \<Longrightarrow> s_disj_fs (loc m0) (?f (xs!n) s)"
        proof -
          fix x assume "s_disj_fs (loc m0) x"
          moreover have
            "s_disj_fs
              (loc m0)
              (arange_safe
                (finsert (fst (write (adata.Array ds) m0)) s)
                (snd (write (adata.Array ds) m0))
                (xs ! n))"
          proof -
            have "(ds!n) \<in> set ds" using Suc(2) by (simp add: xs2)
            moreover have "\<forall>l\<ge>length (snd (fold_map write (take n ds) m0)).
                           l < length (snd (write (ds!n) (snd (fold_map write (take n ds) m0))))
                           \<longrightarrow> l |\<notin>| (finsert (fst (write (adata.Array ds) m0)) s)"
              using range_notin_s[OF \<open>n < length ds\<close> \<open>n < length xs\<close> xs3 Array(2)] by blast
            ultimately have "s_disj_fs (loc (snd (fold_map write (take n ds) m0)))
                 (arange_safe (finsert (fst (write (adata.Array ds) m0)) s)
                   (snd (write (ds!n) (snd (fold_map write (take n ds) m0))))
                   (fst (write (ds!n) (snd (fold_map write (take n ds) m0)))))"
              using Array by blast
            then have "s_disj_fs (loc (snd (fold_map write (take n ds) m0)))
                 (arange_safe (finsert (fst (write (adata.Array ds) m0)) s)
                   (snd (write (ds!n) (snd (fold_map write (take n ds) m0))))
                   (xs ! n))"
              using xs3 by (metis Suc.prems Suc_le_eq)
            moreover from \<open>n < length ds\<close> have "prefix
                 (snd (write (ds ! n) (snd (fold_map write (take n ds) m0))))
                 (snd (write (adata.Array ds) m0))"
              using write_sprefix_take sprefix_prefix by blast
            ultimately have "s_disj_fs (loc (snd (fold_map write (take n ds) m0)))
                 (arange_safe (finsert (fst (write (adata.Array ds) m0)) s)
                   (snd (write (adata.Array ds) m0))
                   (xs ! n))"
              using a_data.range_safe_prefix[of "(snd (write (ds ! n) (snd (fold_map write (take n ds) m0))))"]
              unfolding s_disj_fs_def pred_some_def by (auto simp del: a_data.range_safe.simps) 
            moreover have "prefix m0 (snd (fold_map write (take n ds) m0))"
              using fold_map_prefix[of "write"]
              by (metis write_sprefix prod.collapse sndI sprefix_prefix)
            ultimately show ?thesis
              using s_disj_fs_prefix[of m0 " (snd (fold_map write (take n ds) m0))"] by blast
          qed
          ultimately show "s_disj_fs (loc m0) (?f (xs!n) x)"
            by (auto simp add:s_disj_fs_def pred_some_def)
        qed
        ultimately show ?case by simp
      qed
    qed
  qed
  ultimately show ?case by simp
qed

corollary write_arange:
  assumes "write cd m0 = (l, m)"
  shows "s_disj_fs (loc m0) (arange m l)"
  using write_arange_safe
  unfolding a_data.range_def
  by (metis assms fempty_iff fst_conv snd_conv)

lemma fold_map_write_arange:
  assumes "write (adata.Array ds) m0 = (l, m)"
    and "j < length ds"
    and "i < j"
  shows "s_disj_fs
          (loc (snd (write (ds ! i) (snd (fold_map write (take i ds) m0)))))
          (arange m (fst (write (ds ! j) (snd (fold_map write (take j ds) m0)))))"
  using assms(3,1,2)
proof -
  from assms write_obtain[of ds m0] obtain l' m'
    where *: "write (ds ! j) (snd (fold_map write (take j ds) m0)) = (l', m')"
      and **:"prefix m' m"
    by (metis K.cases snd_conv)
  moreover from * have
    ***: "s_disj_fs (loc (snd (fold_map write (take j ds) m0))) (arange m' l')"
    using write_arange[where ?m0.0="snd (fold_map write (take j ds) m0)"] by auto
  moreover from *** obtain x where "arange m' l' = Some x"
    unfolding s_disj_fs_def pred_some_def by auto
  then have "arange m' l' = arange m l'"
    using assms * ** by (metis a_data.range_def a_data.range_safe_prefix)
  moreover have
    "loc (snd (write (ds ! i) (snd (fold_map write (take i ds) m0))))
    \<subseteq> loc (snd (fold_map write (take j ds) m0))" using assms
    by (metis (no_types, lifting) Suc_leI fold_map_take_snd loc_write_take order.strict_trans)
  ultimately show ?thesis unfolding s_disj_fs_def pred_some_def by auto
qed

theorem write_loc_safe:
  assumes "\<forall>l \<ge> length m0. l < length (snd (write cd m0)) \<longrightarrow> \<not> l |\<in>| s"
  shows
    "s_union_fs
      (loc (snd (write cd m0)))
      (loc m0)
      (arange_safe s (snd (write cd m0)) (fst (write cd m0)))
     \<and> (\<forall>x |\<in>| the (arange_safe s (snd (write cd m0)) (fst (write cd m0))).
          x < (length (snd (write cd m0))))"
  using assms
proof (induction cd arbitrary: m0 s)
  case (Value x)
  then show ?case
    by (auto simp add: s_union_fs_def pred_some_def length_append_def case_memory_def loc_def)
next
  case (Array ds)
  define f where "f =
    (\<lambda>x y. y
      \<bind> (\<lambda>y'.
        (arange_safe (finsert (fst (write (Array ds) m0)) s)
          (snd (write (Array ds) m0)) x)
         \<bind> (\<lambda>l. Some (l |\<union>| y'))))"
  from write_obtain obtain xs
    where xs1: "snd (write (Array ds) m0) $ fst (write (Array ds) m0) = Some (mdata.Array xs)"
      and xs2: "length xs = length ds"
      and xs3: "\<forall>n < length xs.
        xs!n < fst (write (Array ds) m0) \<and>
        xs!n = fst (write (ds!n) (snd (fold_map write (take n ds) m0))) \<and>
         prefix (snd (write (ds ! n) (snd (fold_map write (take n ds) m0)))) (snd (write (adata.Array ds) m0))"
    by metis

  have xs0: "\<not> fst (write (Array ds) m0) |\<in>| s" using Array(2)
    by (metis less_Suc_eq_le write_length_inc write_length_suc nth_safe_length xs1)
  then have "arange_safe s
                    (snd (write (adata.Array ds) m0))
                    (fst (write (adata.Array ds) m0))
                 = fold f xs (Some {|fst (write (Array ds) m0)|})"
    using xs1 by (simp add:case_memory_def f_def) 
  moreover have
    "s_union_fs
      (loc (snd (write (adata.Array ds) m0)))
      (loc m0)
      (fold f xs (Some {|fst (write (Array ds) m0)|}))
    \<and> (\<forall>x |\<in>| the (fold f xs (Some {||})). x < fst (write (adata.Array ds) m0))
    \<and> (fold f xs (Some {||})) \<noteq> None"
    (is "?UNION ds xs")
  proof (rule take_all[where ?P = "\<lambda>xs' ys'. ?UNION ys' xs'"])
    show "\<forall>n\<le>length xs. ?UNION (take n ds) (take n xs)"
    proof (rule allI, rule impI)
      fix n
      assume "n \<le> length xs"
      then show "?UNION (take n ds) (take n xs)"
      proof (induction n)
        case 0
        then show ?case by (auto simp add:s_union_fs_def pred_some_def loc_def length_append_def)
      next
        case (Suc n)
        then have "n < length xs" by simp
        then have "n < length ds" "n \<le> length xs" using xs2 by simp+
        have *: "prefix (take n ds) (take (Suc n) ds)"
          unfolding prefix_def Suc(1) by (metis \<open>n < length ds\<close> take_hd_drop)

        let ?s="(finsert (fst (write (adata.Array ds) m0)) s)"
        let ?B="(snd (write (ds ! n) (butlast (snd (write (adata.Array (take n ds)) m0)))))"
        let ?C="(fst (write (ds ! n) (butlast (snd (write (adata.Array (take n ds)) m0)))))"
        let ?A="(butlast (snd (write (adata.Array (take n ds)) m0)))"

        have a3: "(fold f (take n xs) (Some {||})) \<noteq> None" using Suc by simp

        have
          "\<forall>l\<ge>length (butlast (snd (write (adata.Array (take n ds)) m0))).
             l < length (snd (write (ds ! n) (butlast (snd (write (adata.Array (take n ds)) m0)))))
          \<longrightarrow> l |\<notin>| finsert (fst (write (adata.Array ds) m0)) s"
          using length_write_write[OF \<open>n < length ds\<close> Array(2)] xs3
          by (meson \<open>n < length xs\<close>)
        then have a4: "arange_safe ?s ?B ?C \<noteq> None"
          using Array(1)[of
              "ds!n"
              "(butlast (snd (write (adata.Array (take n ds)) m0)))"
              "(finsert (fst (write (adata.Array ds) m0)) s)"]
          unfolding s_union_fs_def pred_some_def
          using \<open>n < length ds\<close> nth_mem by blast
        from a4 have a5: "arange_safe ?s
                      (snd (write (Array ds) m0))
                      ((fst (write (ds!n) (snd (fold_map write (take n ds) m0))))) \<noteq> None"
          using xs3 \<open>n \<le> length xs\<close>
            a_data.range_safe_prefix[of
              "(snd (write (ds ! n) (butlast (snd (write (adata.Array (take n ds)) m0)))))"
              "(snd (write (Array ds) m0))" "(finsert (fst (write (adata.Array ds) m0)) s)"]
            butlast_write[of "(take n ds)" m0]
          apply (auto simp del:write.simps a_data.range_safe.simps)
          by (metis \<open>n < length xs\<close>)
        have a6:
            "fset (the (fold f (take n xs) (Some {||})))
            = loc (butlast (snd (write (adata.Array (take n ds)) m0))) - loc m0"
        proof (rule s_disj_union_fs)
          show "s_disj_fs (loc m0) (fold f (take n xs) (Some {||}))"
          proof -
            have
              "s_disj_fs
                (loc m0)
                (arange_safe s (snd (write (adata.Array ds) m0)) (fst (write (adata.Array ds) m0)))"
              using write_arange_safe[OF Array(2)] by simp
            then have "s_disj_fs (loc m0) (fold f xs (Some {|fst (write (Array ds) m0)|}))"
              using xs0 xs1 unfolding f_def by (auto simp add: case_memory_def)
            moreover have "s_disj_fs (loc m0) (Some {|fst (write (adata.Array ds) m0)|})"
              unfolding s_disj_fs_def pred_some_def loc_def
              using fold_map_mono write_length_inc[of m0 "(adata.Array ds)"]
              by (auto split:prod.split simp add:length_append_def)
            ultimately have
              "s_disj_fs
                (loc m0)
                (fold f (take n xs) (Some {|fst (write (Array ds) m0)|}))"
              unfolding f_def
              using s_disj_fs_loc_fold[of
                  m0
                  "arange_safe (finsert (fst (write (adata.Array ds) m0)) s) (snd (write (adata.Array ds) m0))"
                  xs "Some {|fst (write (adata.Array ds) m0)|}" n] by simp
            moreover from a3 have "the (fold f (take n xs) (Some {|fst (write (Array ds) m0)|})) =
            the (fold f (take n xs) (Some {||})) |\<union>| {|fst (write (Array ds) m0)|}"
              unfolding f_def using fold_none_the_fold[of
                  "arange_safe (finsert (fst (write (adata.Array ds) m0)) s) (snd (write (adata.Array ds) m0))"
                  "(take n xs)" "{||}" "{|fst (write (adata.Array ds) m0)|}"] by auto
            ultimately have "s_disj_fs (loc m0) (fold f (take n xs) (Some {||}))"
              unfolding s_disj_fs_def pred_some_def
              using a3 by auto
            then show ?thesis unfolding f_def
              using s_disj_fs_loc_fold[of
              m0
              "arange_safe (finsert (fst (write (adata.Array ds) m0)) s) (snd (write (adata.Array ds) m0))"
              xs "Some {||}" n] by simp
          qed
        next
          from Suc(1)[OF \<open>n \<le> length xs\<close>] have
            "s_union_fs
              (loc (snd (write (adata.Array (take n ds)) m0)))
              (loc m0)
              (fold f (take n xs) (Some {|fst (write (adata.Array (take n ds)) m0)|}))"
            by simp
          then show
            "s_union_fs
              (loc (butlast (snd (write (adata.Array (take n ds)) m0))))
              (loc m0)
              (fold f (take n xs) (Some {||}))"
          proof (rule s_union_fs_s_union_fs_diff[OF _ _ _ a3])
            show "loc (butlast (snd (write (adata.Array (take n ds)) m0))) =
              loc (snd (write (adata.Array (take n ds)) m0)) - {fst (write (adata.Array (take n ds)) m0)}"
              unfolding loc_def using write_length_suc[of "adata.Array (take n ds)" m0] by fastforce
          next
            have "fst (write (adata.Array (take n ds)) m0) |\<notin>|
            the (fold f (take n xs) (Some {||}))" using Suc(1)[OF \<open>n \<le> length xs\<close>]
              unfolding loc_def by blast
            then show "the (fold f (take n xs) (Some {||})) =
            the (fold f (take n xs) (Some {|fst (write (adata.Array (take n ds)) m0)|})) |-|
            {|fst (write (adata.Array (take n ds)) m0)|}"
              using fold_insert_same[of "fst (write (adata.Array (take n ds)) m0)" _ n xs "{||}"]
              unfolding f_def by blast
          next
            show "fst (write (adata.Array (take n ds)) m0) \<notin> loc m0"
              by (metis loc_def mem_Collect_eq write_length_inc write_length_suc not_less_eq)
          qed
        qed  

        have a7:"
          the ((
            arange_safe ?s
              (snd (write (Array ds) m0))
              ((fst (write (ds!n) (snd (fold_map write (take n ds) m0)))))))
           |\<inter>| the (fold f (take n xs) (Some {||})) = {||}"
        proof -
          have
            "arange_safe ?s
              (snd (write (Array ds) m0))
              ((fst (write (ds!n) (snd (fold_map write (take n ds) m0)))))
          = arange_safe (finsert (fst (write (adata.Array ds) m0)) s) ?B ?C"
          proof -
            have "prefix ?B (snd (write (Array ds) m0))"
              using xs3 by (metis \<open>n < length xs\<close> butlast_write)
            then have
              "arange_safe ?s ?B ?C
              = arange_safe ?s (snd (write (adata.Array ds) m0)) ?C"
              using a_data.range_safe_prefix[of ?B "(snd (write (Array ds) m0))" ?s] a4
              by fastforce
            moreover have
              "butlast (snd (write (adata.Array (take n ds)) m0))
              = snd (fold_map write (take n ds) m0)"
              using butlast_write by auto
            ultimately show ?thesis by auto
          qed
          moreover have "loc ?A \<inter> fset (the (arange_safe ?s ?B ?C)) = {}"
          proof -
            have "s_disj_fs (loc ?A) (arange_safe ?s ?B ?C)"
            proof (rule write_arange_safe)
              show "\<forall>l\<ge>length ?A. l < length ?B \<longrightarrow> l |\<notin>| ?s"
                using length_write_write[OF \<open>n < length ds\<close> Array(2)] xs3 \<open>n < length xs\<close> by blast
            qed
            then show ?thesis unfolding s_disj_fs_def pred_some_def by auto
          qed
          ultimately show ?thesis using a6 by fastforce
        qed

        show ?case
        proof
          show "s_union_fs (loc (snd (write (adata.Array (take (Suc n) ds)) m0))) (loc m0)
           (fold f (take (Suc n) xs) (Some {|fst (write (adata.Array (take (Suc n) ds)) m0)|}))"
          proof (rule s_union_fs_s_union_fs_union[OF conjunct1[OF Suc(1)[OF \<open>n \<le> length xs\<close>]]])
            show "(loc (snd (write (adata.Array (take (Suc n) ds)) m0))) =
            loc (snd (write (adata.Array (take n ds)) m0))
              - {length (snd (write (adata.Array (take n ds)) m0)) - 1}
              \<union> (insert (length (snd (write (ds!n) (butlast (snd (write (adata.Array (take n ds)) m0))))))
                  (loc (snd (write (ds!n) (butlast (snd (write (adata.Array (take n ds)) m0)))))
                  - (loc (butlast (snd (write (adata.Array (take n ds)) m0))))))"
              apply (auto simp add:loc_def length_append_def split:prod.split)
              using fold_map_take_snd[OF \<open>n < length ds\<close>] apply (metis less_Suc_eq snd_conv)
              using fold_map_take_snd[OF \<open>n < length ds\<close>] apply (metis less_Suc_eq snd_conv)
              using fold_map_take_snd[OF \<open>n < length ds\<close>] apply (metis lessI snd_conv)
              using write_fold_map_mono[OF *, of m0] unfolding prefix_def apply auto[1]
              using fold_map_take_snd[OF \<open>n < length ds\<close>] apply (metis less_SucI snd_conv)
              done
          next
            show "{length (snd (write (adata.Array (take n ds)) m0)) - 1} \<inter> loc m0 = {}"
              using write_length_inc[of m0 "(adata.Array (take n ds))"] unfolding loc_def by simp
          next
            show "{length (snd (write (adata.Array (take n ds)) m0)) - 1}
                  = fset {|(fst (write (Array (take n ds)) m0))|}"
              using write_length_suc[of "adata.Array (take n ds)"] by simp
          next
            show "insert (length ?B) (loc ?B - loc ?A)
                = fset (the (Some (finsert
                    (fst (write (adata.Array (take (Suc n) ds)) m0))
                    (the (f (xs!n) (fold f (take n xs) (Some {||})))
                      |-| (the (fold f (take n xs) (Some {||})))))))"
            proof -
              have "length ?B = (fst (write (adata.Array (take (Suc n) ds)) m0))"
                using write_Array_take_Suc
                by (metis \<open>n < length ds\<close>)
              moreover have "(loc ?B - loc ?A)
                    = fset (the (f (xs!n) (fold f (take n xs) (Some {||})))
                      |-| (the (fold f (take n xs) (Some {||}))))"
              proof -
                have "(loc ?B - loc ?A)
                 = fset (the (arange_safe (finsert (fst (write (adata.Array ds) m0)) s) ?B ?C))"
                proof (rule s_union_fs_diff)
                  have "ds ! n \<in> set ds"
                    by (simp add: \<open>n < length ds\<close>)
                  moreover have "\<forall>l\<ge>length ?A. l < length ?B \<longrightarrow> l |\<notin>| ?s"
                    using length_write_write[OF \<open>n < length ds\<close> Array(2)] \<open>n < length xs\<close> xs3
                    by blast
                  ultimately show "s_union_fs (loc ?B) (loc ?A) (arange_safe ?s ?B ?C)"
                    using Array(1) by blast
                next
                  show "loc ?A \<inter> fset (the (arange_safe ?s ?B ?C)) = {}"
                  proof -
                    have "s_disj_fs (loc ?A) (arange_safe ?s ?B ?C)"
                    proof (rule write_arange_safe)
                      show "\<forall>l\<ge>length ?A. l < length ?B \<longrightarrow> l |\<notin>| ?s"
                        using length_write_write[OF \<open>n < length ds\<close> Array(2)] xs3 \<open>n < length xs\<close>
                        by blast
                  qed
                  then show ?thesis unfolding s_disj_fs_def pred_some_def by auto
                qed
              qed
                moreover have
                  "fset (the (arange_safe ?s ?B ?C))
                  = fset (the (f (xs!n) (fold f (take n xs) (Some {||})))
                    |-| (the (fold f (take n xs) (Some {||}))))"
                proof -
                  from a3 have
                    "(\<lambda>x y. y \<bind> (\<lambda>y'. (arange_safe ?s (snd (write (Array ds) m0)) x)
                                   \<bind> (\<lambda>l. Some (l |\<union>| y')))) (xs!n) (fold f (take n xs) (Some {||}))
                    = (arange_safe ?s
                        (snd (write (Array ds) m0))
                        ((fst (write (ds!n) (snd (fold_map write (take n ds) m0))))))
                      \<bind> (\<lambda>l. Some (l |\<union>| the (fold f (take n xs) (Some {||}))))"
                    using xs3 \<open>n < length xs\<close> by fastforce
                  moreover from a5 have
                    "(arange_safe ?s
                      (snd (write (Array ds) m0))
                      ((fst (write (ds!n) (snd (fold_map write (take n ds) m0))))))
                     \<bind> (\<lambda>l. Some (l |\<union>| the (fold f (take n xs) (Some {||}))))
                    = Some (the (
                        arange_safe ?s
                          (snd (write (Array ds) m0))
                          ((fst (write (ds!n) (snd (fold_map write (take n ds) m0))))))
                      |\<union>| the (fold f (take n xs) (Some {||})))"
                    by fastforce
                  moreover from a7 have
                    "the
                      (arange_safe ?s
                        (snd (write (Array ds) m0))
                        ((fst (write (ds!n) (snd (fold_map write (take n ds) m0))))))
                      |\<union>| the (fold f (take n xs) (Some {||}))
                      |-| (the (fold f (take n xs) (Some {||})))
                    = the
                        (arange_safe ?s
                          (snd (write (Array ds) m0))
                          ((fst (write (ds!n) (snd (fold_map write (take n ds) m0))))))"
                    by blast
                  ultimately have
                    "the (
                      (\<lambda>x y. y \<bind> (\<lambda>y'. (arange_safe ?s (snd (write (Array ds) m0)) x)
                        \<bind> (\<lambda>l. Some (l |\<union>| y')))) (xs!n) (fold f (take n xs) (Some {||})))
                      |-| (the (fold f (take n xs) (Some {||})))
                  = the (
                      arange_safe ?s
                        (snd (write (Array ds) m0))
                        (fst (write (ds!n) (snd (fold_map write (take n ds) m0)))))"
                    by simp
                  moreover have "prefix ?B (snd (write (Array ds) m0))"
                    using xs3 by (metis \<open>n < length xs\<close> butlast_write)
                  moreover have "?C = (fst (write (ds!n) (snd (fold_map write (take n ds) m0))))"
                    by (metis butlast_write)
                  ultimately show ?thesis
                    using a_data.range_safe_prefix[of ?B "(snd (write (Array ds) m0))" ?s]
                    f_def a4 by force
                qed
                ultimately show ?thesis by blast
              qed
              ultimately show ?thesis by simp
            qed
          next
            show "fold f (take (Suc n) xs) (Some {|fst (write (adata.Array (take (Suc n) ds)) m0)|}) =
                  Some (the (fold f (take n xs) (Some {|fst (write (adata.Array (take n ds)) m0)|}))
                  |-| {|(fst (write (adata.Array (take n ds)) m0))|}
                      |\<union>| the (Some (finsert
                        (fst (write (adata.Array (take (Suc n) ds)) m0))
                        (the (f (xs ! n) (fold f (take n xs) (Some {||})))
                          |-| the (fold f (take n xs) (Some {||}))))))"
            (is "?f (Suc n) = Some (the (?f n) |-| {|?s n|} |\<union>| the (Some (finsert (?s (Suc n)) ?r)))")
            proof -
              have "?f (Suc n) = fold f (take (Suc n) xs) (Some {||}) \<bind> Some \<circ> finsert (?s (Suc n))"
                using fold_some_some Suc(2) unfolding f_def by fast
              also have
                "fold f (take (Suc n) xs) (Some {||})
                  = f (xs ! n) (fold f (take n xs) (Some {||}))"
                using fold_take[OF \<open>n < length xs\<close>] .
              also have "(fold f (take n xs) (Some {||})) = Some ((the (?f n)) |-| {|?s n|})"
                unfolding f_def
              proof (rule fold_some_diff)
                have "fst (write (adata.Array (take n ds)) m0)
                  \<notin> loc (butlast (snd (write (adata.Array (take n ds)) m0)))"
                  unfolding loc_def using write_length_suc[of "(adata.Array (take n ds))"] by simp
                then show
                  "fst (write (adata.Array (take n ds)) m0) |\<notin>|
                  the (fold
                   (\<lambda>x y. y \<bind>
                     (\<lambda>y'.
                         arange_safe
                          (finsert (fst (write (adata.Array ds) m0)) s)
                          (snd (write (adata.Array ds) m0))
                          x
                      \<bind> (\<lambda>l. Some (l |\<union>| y'))))
                   (take n xs) (Some {||}))"
                  using a6 unfolding f_def by simp
              next
                from a3 show
                  "fold (\<lambda>x y. y \<bind>
                    (\<lambda>y'. arange_safe (finsert (fst (write (adata.Array ds) m0)) s)
                      (snd (write (adata.Array ds) m0)) x \<bind> (\<lambda>l. Some (l |\<union>| y')))) (take n xs) (Some {||})
                   \<noteq> None"
                  unfolding f_def by auto
              qed
              finally have
                "?f (Suc n) = f (xs ! n) (Some (the (?f n) |-| {|?s n|})) \<bind> Some \<circ> finsert (?s (Suc n))" .
              moreover from a7 have
                "the (arange_safe (finsert (fst (write (adata.Array ds) m0)) s)
                  (snd (write (adata.Array ds) m0)) (xs ! n))
                |\<inter>| the (fold f (take n xs) (Some {||})) = {||}" using xs3 f_def by (metis \<open>n < length xs\<close>)
              moreover from a5 have
                "arange_safe (finsert (fst (write (adata.Array ds) m0)) s)
                  (snd (write (adata.Array ds) m0)) (xs ! n) \<noteq> None" using xs3
                by (simp add: \<open>n < length xs\<close>)
              ultimately show ?thesis using a3 unfolding f_def by auto
            qed
          qed
        next
          show
            "(\<forall>x|\<in>|the (fold f (take (Suc n) xs) (Some {||})).
               x < fst (write (adata.Array (take (Suc n) ds)) m0))
             \<and> fold f (take (Suc n) xs) (Some {||}) \<noteq> None"
          proof
            show
              "\<forall>x|\<in>|the (fold f (take (Suc n) xs) (Some {||})).
                x < fst (write (adata.Array (take (Suc n) ds)) m0)"
            proof (rule ballI)
              fix x assume "x |\<in>| the (fold f (take (Suc n) xs) (Some {||}))"
              then have
                "x |\<in>| the ((\<lambda>x y. y
                  \<bind> (\<lambda>y'.
                    (arange_safe (finsert (fst (write (Array ds) m0)) s)
                      (snd (write (Array ds) m0)) x)
                     \<bind> (\<lambda>l. Some (l |\<union>| y')))) (xs ! n) (fold f (take n xs) (Some {||})))"
                using fold_take[OF \<open>n < length xs\<close>]
                unfolding f_def by (rule back_subst)
              moreover obtain y where y_def: "fold f (take n xs) (Some {||}) = Some y"
                using a3 by auto
              moreover obtain z
                where z_def:
                  "arange_safe
                    (finsert (fst (write (adata.Array ds) m0)) s)
                    (snd (write (adata.Array ds) m0))
                    (xs ! n)
                  = Some z"
                using a5 xs3 using \<open>n < length xs\<close> by auto
              ultimately consider "x |\<in>| y" | "x |\<in>| z"
                by (auto simp del:a_data.range_safe.simps write.simps)
              then show "x < fst (write (adata.Array (take (Suc n) ds)) m0)"
              proof cases
                case 1
                moreover have
                  "fst (write (adata.Array (take n ds)) m0)
                    < fst (write (adata.Array (take (Suc n) ds)) m0)"
                  apply (auto split:prod.split simp add:length_append_def)
                  by (metis \<open>n < length ds\<close> fold_map_take_snd write_length_inc snd_eqD)
                ultimately show ?thesis using Suc(1)[OF \<open>n \<le> length xs\<close>] y_def by auto
              next
                case 2
                have
                  "\<forall>l\<ge>length (snd (fold_map write (take n ds) m0)).
                    l < length (snd (write (ds ! n) (snd (fold_map write (take n ds) m0))))
                   \<longrightarrow> l |\<notin>| finsert (fst (write (adata.Array ds) m0)) s"
                  using range_notin_s[OF \<open>n < length ds\<close> \<open>n < length xs\<close> _ Array(2)] xs3 by blast
                then have "(\<forall>x|\<in>|the (arange_safe (finsert (fst (write (adata.Array ds) m0)) s)
                   (snd (write (ds ! n) (snd (fold_map write (take n ds) m0))))
                   (fst (write (ds ! n) (snd (fold_map write (take n ds) m0))))).
                   x < (length (snd (write (ds ! n) (snd (fold_map write (take n ds) m0))))))"
                  using
                    Array(1)[of
                      "(ds ! n)"
                      "(snd (fold_map write (take n ds) m0))"
                      "(finsert (fst (write (adata.Array ds) m0)) s)"]
                    \<open>n < length ds\<close> nth_mem by blast
                moreover from a4 have
                  "x|\<in>|the (arange_safe (finsert (fst (write (adata.Array ds) m0)) s)
                  (snd (write (ds ! n) (snd (fold_map write (take n ds) m0))))
                  (fst (write (ds ! n) (snd (fold_map write (take n ds) m0)))))"
                  using 2 xs3 z_def \<open>n < length xs\<close> butlast_write a_data.range_safe_prefix
                  by (smt (verit, del_insts) option.exhaust_sel option.sel)
                ultimately have
                  "x < (length (snd (write (ds ! n) (snd (fold_map write (take n ds) m0)))))"
                  by simp
                then show ?thesis 
                  apply (auto split:prod.split simp add:length_append_def)
                  using fold_map_take_snd[OF \<open>n < length ds\<close>, of "write" m0] by simp
              qed
            qed
          next
            have "f (xs ! n) (fold f (take n xs) (Some {||})) \<noteq> None"
            proof -
              from Suc obtain x where "(fold f (take n xs) (Some {||})) = x" by simp
              then show ?thesis using \<open>n < length xs\<close> a3 a5 not_None_eq xs3 unfolding f_def by auto
            qed
            then show "fold f (take (Suc n) xs) (Some {||}) \<noteq> None"
              using fold_take[OF \<open>n < length xs\<close>, of f "(Some {||})"]
              by simp
          qed
        qed
      qed
    qed
  qed  (rule xs2)
  moreover have
    "(\<forall>x|\<in>|the (fold f xs (Some {|fst (write (adata.Array ds) m0)|})).
       x < (length (snd (write (adata.Array ds) m0))))"
  proof
    fix x
    assume *: "x |\<in>| the (fold f xs (Some {|fst (write (adata.Array ds) m0)|}))"
    have "fold f xs (Some ({||} |\<union>| {|fst (write (adata.Array ds) m0)|})) \<noteq> None"
      using calculation(2) unfolding s_union_fs_def pred_some_def by auto
    with *
    consider "x |\<in>| the (fold f xs (Some {||}))"
           | "x |\<in>| {| fst (write (adata.Array ds) m0) |}"
      using fold_none_the_fold[where ?X="{||}" and ?Y="{|fst (write (adata.Array ds) m0)|}"]
      unfolding f_def by fastforce
    then show "x < (length (snd (write (adata.Array ds) m0)))"
    proof cases
      case 1
      then show ?thesis using calculation(2) write_length_suc[of "(adata.Array ds)" m0] by auto
    next
      case 2
      then show ?thesis
        by (metis fsingletonE lessI write_length_suc)
    qed
  qed
  ultimately show ?case by simp
qed

corollary write_loc:
  assumes "write cd m0 = (l, m)"
  shows "s_union_fs (loc m) (loc m0) (arange m l)"
  using assms write_loc_safe unfolding a_data.range_safe_prefix
  by (metis a_data.range_def fempty_iff fst_conv snd_conv)

lemma fold_map_write_loc:
  assumes "write (adata.Array ds) m0 = (l, m)"
     and "i < length ds"
     and "i' = fst (write (ds ! i) (snd (fold_map write (take i ds) m0)))"
   shows "fs_subs_s
            (arange m i')
            (loc (snd (write (ds ! i ) (snd (fold_map write (take i ds) m0)))))"
  using assms
proof -
  from assms(3)
  have
    "s_union_fs
      (loc (snd (write (ds ! i) (snd (fold_map write (take i ds) m0)))))
      (loc (snd (fold_map write (take i ds) m0)))
      (arange (snd (write (ds ! i) (snd (fold_map write (take i ds) m0)))) i')"
    using write_loc[of
          "ds ! i"
          "snd (fold_map write (take i ds) m0)"
          i'
          "snd (write (ds ! i) (snd (fold_map write (take i ds) m0)))"]
    by simp
  then obtain L
    where L_def: "arange (snd (write (ds ! i) (snd (fold_map write (take i ds) m0)))) i'
            = Some L"
      and "loc (snd (write (ds ! i) (snd (fold_map write (take i ds) m0))))
        = loc (snd (fold_map write (take i ds) m0)) \<union> fset L"
    unfolding s_union_fs_def pred_some_def by blast
  moreover from assms(1,2) write_obtain[of ds m0] have
    "prefix (snd (write (ds ! i) (snd (fold_map write (take i ds) m0)))) m" by auto
  with L_def have "arange m i' = Some L" using a_data.range_prefix by blast
  ultimately show ?thesis unfolding fs_subs_s_def pred_some_def by blast
qed

lemma prefix_write_range_safe_same:
  assumes "prefix (snd (write (ds ! n) (snd (fold_map write (take n ds) m0)))) m"
      and "arange_safe s m y = Some L'"
      and "y = fst (write (ds ! n) (snd (fold_map write (take n ds) m0)))"
      and "\<forall>l\<ge>length (snd (fold_map write (take n ds) m0)).
            l < length (snd (write (ds ! n) (snd (fold_map write (take n ds) m0))))
          \<longrightarrow> l |\<notin>| s"
    shows "arange_safe s (snd (write (ds ! n) (snd (fold_map write (take n ds) m0)))) y = Some L'"
proof -
  from assms(3) obtain LL
    where "arange_safe s (snd (write (ds ! n) (snd (fold_map write (take n ds) m0)))) y = Some LL"
    using write_loc_safe[OF assms(4)] unfolding s_union_fs_def pred_some_def by blast
  then show ?thesis using assms(1,2)
    by (metis a_data.range_safe_prefix)
qed

lemma prefix_write_nth_same:
  assumes "m $ x = Some (mdata.Array xs)"
      and "fst (write (ds ! n) (snd (fold_map write (take n ds) m0))) = y"
      and "arange_safe s m y = Some L'"
      and "x |\<in>| L'"
      and "prefix (snd (write (ds ! n) (snd (fold_map write (take n ds) m0)))) m"
    shows "snd (write (ds ! n) (snd (fold_map write (take n ds) m0))) $ x = Some (mdata.Array xs)"
proof -
  from assms(2) obtain L
    where "arange (snd (write (ds ! n) (snd (fold_map write (take n ds) m0)))) y = Some L"
      and subs: "fset L \<subseteq> loc (snd (write (ds ! n) (snd (fold_map write (take n ds) m0))))"
    using write_loc[of "ds ! n" "snd (fold_map write (take n ds) m0)"]
    unfolding s_union_fs_def pred_some_def by force
  then have "arange m y = Some L" using a_data.range_prefix[OF assms(5)] by auto
  with assms(4) have "x |\<in>| L"
    by (metis assms(3) bot.extremum a_data.range_def option.inject a_data.range_safe_subset_same)
  with subs obtain l
    where "snd (write (ds ! n) (snd (fold_map write (take n ds) m0))) $ x = Some l"
    unfolding loc_def by auto
  with assms(1,5) show ?thesis by (metis nth_safe_prefix)
qed

section \<open>Memory Init and Memory Copy\<close>

theorem write_aread_safe:
  assumes "\<forall>l \<ge> length m0. l < length (snd (write cd m0)) \<longrightarrow> \<not> l |\<in>| s"
  shows "\<forall>mx. prefix (snd (write cd m0)) mx
        \<longrightarrow> aread_safe s mx (fst (write cd m0)) = Some cd"
  using assms
proof (induction cd arbitrary: m0 s)
  case (Value x)
  then show ?case by (auto simp add: length_append_def case_memory_def prefix_def)
next
  case (Array ds)
  show ?case
  proof (rule allI, rule impI)
    fix mx
    assume 1: "prefix (snd (write (adata.Array ds) m0)) mx"
    from write_obtain obtain xs
      where xs1: "snd (write (Array ds) m0) $ fst (write (Array ds) m0) = Some (mdata.Array xs)"
        and xs2: "length xs = length ds"
        and xs3: "\<forall>n < length xs. xs!n < fst (write (Array ds) m0)
          \<and> xs!n = fst (write (ds!n) (snd (fold_map write (take n ds) m0)))"
      by metis
    moreover have "\<not> fst (write (Array ds) m0) |\<in>| s" using Array(2)
      by (metis less_Suc_eq_le write_length_inc write_length_suc nth_safe_length xs1)
    ultimately have "aread_safe s
                      (snd (write (adata.Array ds) m0))
                      (fst (write (adata.Array ds) m0))
                   = those (map (aread_safe
                      (finsert (fst (write (Array ds) m0)) s)
                      (snd (write (Array ds) m0))) xs)
                     \<bind> Some \<circ> Array" by (simp add:case_memory_def)
    moreover have "those (map (aread_safe
                    (finsert (fst (write (Array ds) m0)) s)
                    (snd (write (Array ds) m0))) xs)
                  = Some ds"
    proof (rule take_all[where ?P = "\<lambda>xs ys. those (map (aread_safe
                                    (finsert (fst (write (Array ds) m0)) s)
                                    (snd (write (Array ds) m0))) xs) = Some ys"])
      show "\<forall>n \<le> length xs. those (map (aread_safe
                  (finsert (fst (write (Array ds) m0)) s)
                  (snd (write (Array ds) m0))) (take n xs))
                = Some (take n ds)"
      proof (rule allI, rule impI)
        fix n
        assume "n \<le> length xs"
        then show "those (map (aread_safe
                (finsert (fst (write (Array ds) m0)) s)
                (snd (write (Array ds) m0))) (take n xs))
              = Some (take n ds)"
        proof (induction n)
          case 0
          then show ?case by simp
        next
          case (Suc n)
          from Suc(2) have "n < length xs" by auto
          then have *: "take (Suc n) xs = (take n xs) @ [xs!n]"
               and **: "take (Suc n) ds = (take n ds) @ [ds!n]"
            apply (rule List.take_Suc_conv_app_nth)
            using \<open>n < length xs\<close> take_Suc_conv_app_nth xs2 by auto
          moreover have ***:
            "aread_safe
              (finsert (fst (write (Array ds) m0)) s)
              (snd (write (Array ds) m0))
              (xs!n)
             = Some (ds!n)"
          proof -
            have "aread_safe (finsert (fst (write (Array ds) m0)) s)
              (snd (write (Array ds) m0))
              (fst (write (ds!n) (snd (fold_map write (take n ds) m0))))
            = Some (ds!n)"
            proof -
              have "ds!n \<in> set ds" using \<open>n < length xs\<close> xs2 by auto
              moreover from \<open>n < length xs\<close> have "n < length ds" using xs2 by simp
              then have
                "prefix
                  (snd (write (ds!n) (snd (fold_map write (take n ds) m0))))
                  (snd (write (Array ds) m0))"
                using write_sprefix_take using sprefix_prefix by blast
              moreover have "\<forall>l\<ge>length (snd (fold_map write (take n ds) m0)).
                l < length (snd (write (ds!n) (snd (fold_map write (take n ds) m0))))
                \<longrightarrow> l |\<notin>| (finsert (fst (write (Array ds) m0)) s)"
              using range_notin_s[OF \<open>n < length ds\<close> \<open>n < length xs\<close> xs3 Array(2)] by blast
              ultimately show ?thesis using Array(1) by blast
            qed
            moreover have "xs!n = fst (write (ds!n) (snd (fold_map write (take n ds) m0)))"
              using xs3 \<open>n < length xs\<close> by simp
            ultimately show ?thesis by simp
          qed
          moreover from \<open>n < length xs\<close> have "n \<le> length xs" by simp
          then have
            "those (map (aread_safe (finsert (fst (write (adata.Array ds) m0)) s)
              (snd (write (adata.Array ds) m0)))
              (take n xs))
             = Some (take n ds)" using Suc(1) xs2 by argo
          ultimately show
            "those (map (aread_safe (finsert (fst (write (adata.Array ds) m0)) s)
              (snd (write (adata.Array ds) m0)))
              (take (Suc n) xs))
             = Some (take (Suc n) ds)" using those_those \<open>n < length xs\<close>
            by fastforce
        qed
      qed
    qed (rule xs2)
    ultimately show "aread_safe s mx (fst (write (adata.Array ds) m0)) = Some (adata.Array ds)"
      by (metis 1 bind.bind_lunit comp_apply a_data.read_safe_prefix)
  qed
qed

corollary write_read:
  assumes "write cd m0 = (l, m)"
      and "prefix m mx"
    shows "aread mx l = Some cd"
  using assms write_aread_safe unfolding a_data.read_def
  by (metis fempty_iff fst_conv snd_conv)

section \<open>Minit and Separation Check\<close>

lemma write_adisjoint_safe:
  assumes "write cd m0 = (l, m1)"
      and "arange_safe s m1 l = Some L"
      and "\<forall>l \<ge> length m0. l < length (snd (write cd m0)) \<longrightarrow> \<not> l |\<in>| s"
    shows "adisjoint m1 L"
  using assms
proof (induction arbitrary: L l m0 rule:write.induct)
  case (1 x m)
  then show ?case unfolding a_data.disjoint_def
    by (auto simp add:length_append_def case_memory_def split:if_split_asm)
next
  case (2 ds m)
  have "\<forall>x |\<in>| L. \<forall>xs. m$x = Some (mdata.Array xs)
    \<longrightarrow> (\<forall>i j i' j' L L'.
          i \<noteq> j \<and> xs $ i = Some i'
          \<and> xs$j = Some j'
          \<and> arange m i' = Some L
          \<and> arange m j' = Some L'
      \<longrightarrow> L |\<inter>| L' = {||})"
  proof
    fix x
    assume "x |\<in>| L"
    then consider
        (1) "x = l"
      | (2) n y L'
      where "n<length ds"
        and "fst (write (ds ! n) (snd (fold_map write (take n ds) m0))) = y"
        and "arange_safe s m y = Some L'"
        and "x |\<in>| L'"
      using write_range_safe_in "2.prems"(1,2) by blast
    then show
      "\<forall>xs. m $ x = Some (mdata.Array xs)
      \<longrightarrow> (\<forall>i j i' j' L L'.
            i \<noteq> j
            \<and> xs $ i = Some i'
            \<and> xs $ j = Some j'
            \<and> arange m i' = Some L
            \<and> arange m j' = Some L'
          \<longrightarrow> L |\<inter>| L' = {||})"
    proof cases
      case 1
      show ?thesis
      proof (rule, rule, rule, rule, rule, rule, rule, rule, rule)
        fix xs i j i' j' L L'
        assume *: "m $ x = Some (mdata.Array xs)"
          and **: "i \<noteq> j
                  \<and> xs $ i = Some i'
                  \<and> xs $ j = Some j'
                  \<and> arange m i' = Some L
                  \<and> arange m j' = Some L'"
        {
          fix i::nat and j and i' and j' and L and L'
          assume "i < j"
            and **: "xs $ i = Some i'
                    \<and> xs $ j = Some j'
                    \<and> arange m i' = Some L
                    \<and> arange m j' = Some L'"
          moreover from 2(2) have
            "snd (write (adata.Array ds) m0) $ fst (write (adata.Array ds) m0)
            = Some (mdata.Array xs)"
            using * 1 by simp
          then have
            "length xs = length ds"
            and 0:  "\<forall>n<length xs.
              xs ! n < fst (write (adata.Array ds) m0) \<and>
              xs ! n = fst (write (ds ! n) (snd (fold_map write (take n ds) m0)))
              \<and> prefix
                  (snd (write (ds ! n) (snd (fold_map write (take n ds) m0))))
                  (snd (write (adata.Array ds) m0))"
            using write_obtain[of ds m0] *
            by (fastforce, metis (mono_tags, lifting) mdata.inject(2) option.inject)
          then have
            "j' = fst (write (ds ! j) (snd (fold_map write (take j ds) m0)))"
            and ***: "prefix
                        (snd (write (ds ! j) (snd (fold_map write (take j ds) m0))))
                        (snd (write (adata.Array ds) m0))"
            by (metis "**" nth_safe_def nth_safe_length option.sel)+
          moreover have "j < length ds" using `length xs = length ds`
            by (metis "**" nth_safe_length)
          then have
            "s_disj_fs
              (loc (snd (write (ds ! i ) (snd (fold_map write (take i ds) m0)))))
              (arange m (fst (write (ds ! j) (snd (fold_map write (take j ds) m0)))))"
            using fold_map_write_arange[OF 2(2), of j i] `i < j` by blast
          ultimately have
            "s_disj_fs
              (loc (snd (write (ds ! i ) (snd (fold_map write (take i ds) m0)))))
              (Some L')"
            using ** by simp
          moreover have
            "fset L \<subseteq> (loc (snd (write (ds ! i ) (snd (fold_map write (take i ds) m0)))))"
          proof -
            from 0 have "i' = fst (write (ds ! i) (snd (fold_map write (take i ds) m0)))"
              by (metis "**" nth_safe_def nth_safe_length option.sel)+
            moreover from `j < length ds` have "i < length ds" using `i<j` by simp
            ultimately have
              "fs_subs_s
                (arange m i')
                (loc (snd (write (ds ! i) (snd (fold_map write (take i ds) m0)))))"
              using fold_map_write_loc[OF 2(2), of i i'] 2(2) ** `j < length ds` `i < j` by simp
            then show ?thesis unfolding fs_subs_s_def pred_some_def using ** by simp
          qed
          ultimately have "L |\<inter>| L' = {||}" unfolding s_disj_fs_def pred_some_def by auto
        } note inner=this

        from ** consider "i < j" | "j < i" by linarith
        then show "L |\<inter>| L' = {||}"
        proof (cases)
          case _: 1
          then show ?thesis using inner ** by blast
        next
          case 2
          then show ?thesis using inner ** by blast
        qed
      qed
    next
      case 22: 2
      from 22(1) have "ds ! n \<in> set ds" by simp
      moreover from 22(2) have
        "write (ds ! n) (snd (fold_map write (take n ds) m0))
        = (y, snd (write (ds ! n) (snd (fold_map write (take n ds) m0))))" by auto
      moreover have
        *: "\<forall>l\<ge>length (snd (fold_map write (take n ds) m0)).
            l < length (snd (write (ds ! n) (snd (fold_map write (take n ds) m0)))) \<longrightarrow> l |\<notin>| s"
        by (metis "2.prems"(3) "22"(1) butlast_write finsertCI fold_map_length fold_map_take_fst
            length_write_write write_fold_map_less)
      moreover have **: "prefix (snd (write (ds ! n) (snd (fold_map write (take n ds) m0)))) m"
        by (metis "2.prems"(1) "22"(1) write_obtain split_pairs)
      then have 7:
        "arange_safe s (snd (write (ds ! n) (snd (fold_map write (take n ds) m0)))) y = Some L'"
        using prefix_write_range_safe_same[OF _ 22(3) _ *] 22(2) by blast
      ultimately have
        "adisjoint (snd (write (ds ! n) (snd (fold_map write (take n ds) m0)))) L'"
        using 2(1)[of
            "ds ! n"
            "(snd (fold_map write (take n ds) m0))"
            y
            "snd (write (ds ! n) (snd (fold_map write (take n ds) m0)))"
            L']
        by simp
      moreover from 22 have "x |\<in>| L'" by blast
      ultimately have
        *: "\<forall>xs. (snd (write (ds ! n) (snd (fold_map write (take n ds) m0)))) $ x
            = Some (mdata.Array xs)
           \<longrightarrow> (\<forall>i j i' j' L L'.
                i \<noteq> j
                \<and> xs $ i = Some i'
                \<and> xs $ j = Some j'
                \<and> arange (snd (write (ds ! n) (snd (fold_map write (take n ds) m0)))) i'
                  = Some L
                \<and> arange (snd (write (ds ! n) (snd (fold_map write (take n ds) m0)))) j'
                  = Some L'
             \<longrightarrow> L |\<inter>| L' = {||})"
        by (simp add: a_data.disjoint_def)
      show ?thesis
      proof (rule, rule, rule, rule, rule, rule, rule, rule, rule)
        fix xs i j i' j' L' L''
        assume ***: "m $ x = Some (mdata.Array xs)"
          and ****: "i \<noteq> j
                    \<and> xs $ i = Some i'
                    \<and> xs $ j = Some j'
                    \<and> arange m i' = Some L'
                    \<and> arange m j' = Some L''"
        moreover have
          *****: "(snd (write (ds ! n) (snd (fold_map write (take n ds) m0)))) $ x
          = Some (mdata.Array xs)"
          using prefix_write_nth_same[OF *** _ 22(3,4) **] "22"(2) by auto
        moreover have
          "arange (snd (write (ds ! n) (snd (fold_map write (take n ds) m0)))) i' = Some L'"
          using a_data.range_safe_prefix_in_range[OF 7 22(4) *****] **** ** by blast
        moreover have
          "arange (snd (write (ds ! n) (snd (fold_map write (take n ds) m0)))) j' = Some L''"
          using a_data.range_safe_prefix_in_range[OF 7 22(4) *****] **** ** by blast
        ultimately show "L' |\<inter>| L'' = {||}" using * by blast
      qed
    qed
  qed
  then show ?case unfolding a_data.disjoint_def
    by (simp add: a_data.range_def arange_safe_def)
qed

corollary write_adisjoint:
  assumes "write a m = (l, m')"
      and "arange m' l = Some L"
    shows "adisjoint m' L"
  using write_adisjoint_safe[OF assms(1), of "{||}"] assms arange_def arange_safe_def data.range_def
  by (metis fempty_iff)

end