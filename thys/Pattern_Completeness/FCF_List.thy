theory FCF_List
  imports 
    FCF_Multiset
    Singleton_List
    Finite_IDL_Solver_Interface
    Pattern_Completeness_List
begin

lemma finite_var_form_pat_pat_complete_list:
  fixes pp::"('f,'v,'s) pat_problem_list" and C
  assumes fvf: "finite_var_form_pat C (pat_list pp)"
    and pp: "pp = pat_of_var_form_list fvf" 
    and dist: "Ball (set fvf) (distinct o map fst)" 
  shows "pat_complete C (pat_list pp) \<longleftrightarrow>
  (\<forall>\<alpha>. (\<forall>v \<in> set (tvars_pat_list pp). \<alpha> v < card_of_sort C (snd v)) \<longrightarrow>
       (\<exists>c \<in> set (map (map snd) fvf).
        \<forall>vs \<in> set c. UNIQ (\<alpha> ` set vs)))"
proof-
  from finite_var_form_imp_of_var_form_pat[OF fvf]
  have vf: "var_form_pat (pat_list pp)".
  have "(\<exists>mp \<in> pat_list pp. \<forall>x. UNIQ {\<alpha> v |v. (Var v, Var x) \<in> mp}) \<longleftrightarrow>
    (\<exists>mpv \<in> set fvf. \<forall>(x,vs) \<in> set mpv. UNIQ (\<alpha> ` set vs))"
    (is "?l \<longleftrightarrow> ?r")
    for \<alpha> :: "_ \<Rightarrow> nat"
  proof safe
    fix mpv
    assume "mpv \<in> set fvf"
      and r: "\<forall>(x,vs) \<in> set mpv. UNIQ (\<alpha> ` set vs)"
    with pp[unfolded pat_of_var_form_list_def] dist
    have mem: "set (match_of_var_form_list mpv) \<in> pat_list pp" 
      and dist: "distinct (map fst mpv)" 
      unfolding pat_list_def by auto  
    show ?l
    proof (intro bexI[OF _ mem] allI)
      fix x
      show "UNIQ {\<alpha> v |v. (Var v, Var x) \<in> set (match_of_var_form_list mpv)}" (is "UNIQ ?vs")
      proof (cases "x \<in> fst ` set mpv")
        case False
        hence vs: "?vs = {}" unfolding match_of_var_form_list_def by force
        show ?thesis unfolding vs using Uniq_False by force
      next
        case True
        then obtain vs where x_vs: "(x,vs) \<in> set mpv" by force
        with r have uniq: "UNIQ (\<alpha> ` set vs)" by auto
        from split_list[OF x_vs] obtain bef aft where mpv: "mpv = bef @ (x,vs) # aft" by auto
        from dist[unfolded arg_cong[OF this, of "map fst"]]
        have x: "x \<notin> fst ` set bef \<union> fst ` set aft" by auto
        hence "\<alpha> ` set vs = ?vs" unfolding match_of_var_form_list_def mpv by force
        with uniq show ?thesis by auto
      qed
    qed
  next
    fix mp
    assume "mp \<in> pat_list pp" and uniq: "\<forall>x. UNIQ {\<alpha> v |v. (Var v, Var x) \<in> mp}" 
    from this[unfolded pp pat_list_def pat_of_var_form_list_def]
    obtain mpv where mem: "mpv \<in> set fvf" and mp: "mp = set (match_of_var_form_list mpv)" by auto
    from dist mem have dist: "distinct (map fst mpv)" by auto
    show "\<exists>mpv\<in>set fvf. \<forall>(x, vs)\<in>set mpv. UNIQ (\<alpha> ` set vs)" 
    proof (intro bexI[OF _ mem], safe)
      fix x vs 
      assume "(x,vs) \<in> set mpv" 
      from split_list[OF this] obtain bef aft where mpv: "mpv = bef @ (x,vs) # aft" by auto
      from dist[unfolded arg_cong[OF this, of "map fst"]]
      have x: "x \<notin> fst ` set bef \<union> fst ` set aft" by auto
      from uniq[rule_format, of x] 
      have "UNIQ {\<alpha> v |v. (Var v, Var x) \<in> mp}" .
      also have "{\<alpha> v |v. (Var v, Var x) \<in> mp} = \<alpha> ` set vs" 
        unfolding mp match_of_var_form_list_def mpv using x by force
      finally show "UNIQ (\<alpha> ` set vs)" .
    qed
  qed
  note finite_var_form_pat_pat_complete[OF fvf, unfolded this]
  note main = this[folded set_tvars_pat_list]
  show ?thesis unfolding main
    by (intro all_cong, force split: prod.splits)
qed


lemma pat_complete_via_cnf:
  assumes fvf: "finite_var_form_pat C (pat_list pp)"
    and pp: "pp = pat_of_var_form_list fvf" 
    and dist: "Ball (set fvf) (distinct o map fst)" 
    and cnf: "cnf = map (map snd) fvf"
  shows "pat_complete C (pat_list pp) \<longleftrightarrow>
  (\<forall>\<alpha>. (\<forall>v \<in> set (concat (concat cnf)). \<alpha> v < card_of_sort C (snd v)) \<longrightarrow>
       (\<exists>c \<in> set cnf. \<forall>vs \<in> set c. UNIQ (\<alpha> ` set vs)))"
  unfolding finite_var_form_pat_pat_complete_list[OF fvf pp dist] cnf[symmetric]
proof (intro all_cong1 arg_cong[of _ _ "\<lambda> x. x \<longrightarrow> _"] ball_cong refl)
  show "set (tvars_pat_list pp) = set (concat (concat cnf))" unfolding tvars_pat_list_def
    cnf pp
    by (force simp: tvars_match_list_def pat_of_var_form_list_def match_of_var_form_list_def)
qed

fun zip_lists :: "nat \<Rightarrow> 'a list list \<Rightarrow> 'a list list" where
  "zip_lists n [] = replicate n []" 
| "zip_lists n (xs # xss) = map2 (#) xs (zip_lists n xss)" 

lemma zip_lists: assumes "\<And> xs. xs \<in> set xss \<Longrightarrow> length xs = n" 
  shows "zip_lists n xss = map (\<lambda> i. map (\<lambda> xs. xs ! i) xss) [0..<n]" 
  using assms
proof (induct xss)
  case Nil
  then show ?case by (auto intro: nth_equalityI)
next
  case (Cons xs xss)
  hence IH: "zip_lists n xss = map (\<lambda>i. map (\<lambda>xs. xs ! i) xss) [0..<n]" 
    and len: "length xs = n" by auto
  show ?case unfolding zip_lists.simps IH map_map using len 
    by (intro nth_equalityI, auto)
qed

fun length_gt_1 where
  "length_gt_1 (x # y # xs) = True" 
| "length_gt_1 _ = False" 

lemma length_gt_1[simp]: "length_gt_1 xs = (length xs > 1)" 
  by (cases xs rule: length_gt_1.cases, auto)

definition uniq_list :: "'a list \<Rightarrow> bool" where
  "uniq_list xs = (xs = [] \<or> is_singleton_list xs)" 

lemma uniq_list[simp]: "uniq_list xs \<longleftrightarrow> UNIQ (set xs)" 
  unfolding uniq_list_def is_singleton_list2
  by (cases xs; auto simp: Uniq_def)


primrec extract_option :: "('a \<Rightarrow> 'b option) \<Rightarrow> 'a list \<Rightarrow> ('a list \<times> 'a \<times> 'b \<times> 'a list)option" where
  "extract_option f [] = None" 
| "extract_option f (x # xs) = (case f x of Some y \<Rightarrow> Some ([], x, y, xs)
        | None \<Rightarrow> map_option (map_prod (Cons x) id) (extract_option f xs))" 

lemma extract_option_Some: assumes "extract_option f xs = Some (bef, x, y, aft)" 
  shows "xs = bef @ x # aft" "f x = Some y" 
  using assms
proof (atomize(full), induct xs arbitrary: bef)
  case (Cons u us)
  show ?case
    by (cases "f u", insert Cons, auto)
qed simp

lemma extract_option_None: "extract_option f xs = None \<longleftrightarrow> Ball (set xs) (\<lambda> x. f x = None)" 
  by (induct xs, auto split: option.splits)



fun sort_of :: "('f \<times> 's,'v \<times> 's)term \<Rightarrow> 's" where
  "sort_of (Fun (f,s) ts) = s" 
| "sort_of (Var (x,s)) = s" 

fun list_Union :: "'a set list \<Rightarrow> 'a set" where
  "list_Union [] = {}" 
| "list_Union (x # xs) = x \<union> list_Union xs" 

lemma list_Union[simp]: "list_Union xs = \<Union> (set xs)" 
  by (induct xs, auto)

fun sorts_of :: "('f \<times> 's,'v \<times> 's)term \<Rightarrow> 's set" where
  "sorts_of (Fun (f,s) ts) = insert s (list_Union (map sorts_of ts))" 
| "sorts_of (Var (x,s)) = {s}" 

definition arg_sorts_of :: "('f \<times> 's,'v \<times> 's)term \<Rightarrow> 's set" where
  "arg_sorts_of t = list_Union (map sorts_of (args t))" 

fun remove_sort :: "('f \<times> 's,'v)term \<Rightarrow> ('f,'v)term" where
  "remove_sort (Var x) = Var x" 
| "remove_sort (Fun (f,s) ts) = Fun f (map remove_sort ts)" 


type_synonym ('f,'s)simple_match_problem_list = "('f,nat \<times> 's)term list list"
type_synonym ('f,'s)simple_match_problem_slist = "('f \<times> 's,nat \<times> 's)term list list"
type_synonym ('f,'s)simple_pat_problem_slist = "('f \<times> 's,nat \<times> 's)term list list list"
type_synonym ('f,'s)tagged_simple_pat_problem_slist = "bool \<times> ('f,'s)simple_pat_problem_slist"

definition search_fun_pp :: "('f,'s)simple_pat_problem_slist \<Rightarrow> _ option" where
  "search_fun_pp pp = extract_option (extract_option (List.extract is_Fun)) pp" 

lemma search_fun_pp_None: assumes "search_fun_pp pp = None" 
  shows "t \<in> \<Union> (\<Union> (set3 pp)) \<Longrightarrow> is_Var t" 
  using assms[unfolded search_fun_pp_def, unfolded extract_option_None extract_None_iff]
  by auto

lemma search_fun_pp_Some: assumes "search_fun_pp pp = Some (p1,mp,(mp1,eqc,(eqc1,t,eqc2),mp2),p2)" 
  shows "pp = p1 @ mp # p2" "mp = mp1 @ eqc # mp2" "eqc = eqc1 @ t # eqc2" "is_Fun t" 
proof (atomize(full), goal_cases)
  case 1
  from extract_option_Some[OF assms[unfolded search_fun_pp_def]]
  have pp: "pp = p1 @ mp # p2" and 
    Some: "extract_option (List.extract is_Fun) mp = Some (mp1, eqc, (eqc1,t,eqc2), mp2)"
    by auto
  from extract_option_Some[OF Some]
  have mp: "mp = mp1 @ eqc # mp2" and
    Some: "List.extract is_Fun eqc = Some (eqc1, t, eqc2)" 
    by auto
  from List.extract_SomeE[OF Some] 
  have eqc: "eqc = eqc1 @ t # eqc2" and 
    t: "is_Fun t" 
    by auto
  show ?case using pp mp eqc t by auto
qed

definition aroot where "aroot = map_option (map_prod fst id) o root" 

definition "bounds_list bnd cnf = (let vars = remdups (concat (concat cnf))
  in map (\<lambda> v. (v, int (bnd v) - 1)) vars)" 

context pattern_completeness_context
begin

fun add_sort :: "('f,nat \<times> 's)term \<Rightarrow> ('f \<times> 's,nat \<times> 's)term" where
  "add_sort (Var x) = (Var x)" 
| "add_sort (Fun f ts) = (let ats = map add_sort ts 
     in (Fun (f, the (C (f, map sort_of ats))) ats))" 

lemma aroot[simp]: "aroot (add_sort t) = root t" 
  by (cases t, auto simp: aroot_def)

lemma remove_add_sort[simp]: "remove_sort (add_sort t) = t" 
  by (induct t, auto simp: o_def intro: nth_equalityI)

lemma is_Var_add_sort[simp]: "is_Var (add_sort t) = is_Var t" 
    by (cases t, auto)

lemma inj_add_sort[simp]: "inj add_sort" 
  using remove_add_sort by (metis injI)

lemma add_sort_inj[simp]: "(add_sort s = add_sort t) = (s = t)" 
  using inj_add_sort[unfolded inj_def] by auto

lemma add_sort: assumes "t : s in \<T>(C,\<V>)" 
  shows "sort_of (add_sort t) = s" 
  using assms
proof (induct)
  case (Var v s)
  then show ?case by (cases v, auto)
next
  case (Fun f ts ss s)
  have map: "map (\<lambda>x. sort_of (add_sort x)) ts = ss" 
    by (intro nth_equalityI, insert Fun(3), auto simp: list_all2_conv_all_nth)
  show ?case unfolding add_sort.simps Let_def map_map o_def map
    using fun_hastypeD[OF Fun(1)] by auto
qed 

definition rel_term :: "('f,nat \<times> 's)term \<Rightarrow> ('f \<times> 's,nat \<times> 's) term \<Rightarrow> bool" where
  "rel_term t st = (st = add_sort t)" 

definition rel_smp :: "('f,'s)simple_match_problem_list 
  \<Rightarrow> ('f,'s)simple_match_problem_slist 
  \<Rightarrow> ('f,'s)simple_match_problem_ms \<Rightarrow> bool" where
  "rel_smp mpl mpsl mpm = (finite_constructor_form_mp (set2 mpl) 
     \<and> mpsl = map (map add_sort) mpl \<and> mpm = mset (map mset mpl))"

abbreviation mset2' where "mset2' mpl \<equiv> mset (map mset mpl)" 
abbreviation mset3' where "mset3' ppl \<equiv> mset (map mset2' ppl)" 

lemma rel_smpD: assumes "rel_smp mpl mpsl mpm"
  shows "finite_constructor_form_mp (set2 mpl)"
    "finite_constructor_form_mp (mset2 mpm)"
    "mpsl = map (map add_sort) mpl" 
    "set2 mpl = mset2 mpm" 
    "mpm = mset2' mpl" 
  using assms unfolding rel_smp_def by (auto simp: image_comp)

(* at the moment, we do not use the full power of the large-sort elimination rule 
   where the individual x- and t-terms
   are calculated, but just check a sufficient criterion *)
definition large_sort_impl_main :: "('f,'s)simple_pat_problem_slist \<Rightarrow> 's \<Rightarrow> ('f,'s)simple_pat_problem_slist option" 
  where "large_sort_impl_main p s = (let
     find_conflict = (\<lambda> mp. (\<exists> eqc \<in> set mp. sort_of (hd eqc) = s))
    in case partition find_conflict p of
      (del, keep) \<Rightarrow> if del \<noteq> [] \<and> length del < cd_sort s \<and> 
          (\<forall> mp \<in> set keep. \<forall> eq \<in> set mp. \<forall> t \<in> set eq. \<forall> x \<in> set (vars_term_list t). snd x \<noteq> s)
       then Some keep 
       else None)" 
 
definition large_sort_impl :: "('f,'s)simple_pat_problem_slist \<Rightarrow> ('f,'s)simple_pat_problem_slist option" where
  "large_sort_impl p = (let
      terms = concat (concat p);
      sorts = remdups (map sort_of terms)
    in map_option (\<lambda> (_,_,p',_). p') (extract_option (large_sort_impl_main p) sorts))" 



(* simplification: remove singletons, duplicates and triv sorts,
   and apply decompose rule and clash *)
function simplify_mp_main :: "('f,'s)simple_match_problem_slist \<Rightarrow> ('f,'s)simple_match_problem_slist \<Rightarrow> ('f,'s)simple_match_problem_slist option" where
  "simplify_mp_main [] mpout = Some mpout" 
| "simplify_mp_main (eqc # mp) mpout = (if is_singleton_list eqc \<or> cd_sort (sort_of (hd eqc)) = 1 
     then simplify_mp_main mp mpout
     else let eqc' = remdups eqc; roots = map aroot eqc' 
        in (if None \<in> set roots 
             then (if Ball (set eqc') (\<lambda> t. Ball (set eqc') (\<lambda> s. \<not> Conflict_Clash (remove_sort s) (remove_sort t)))
          then simplify_mp_main mp (eqc' # mpout) else None)
           else (if is_singleton_list roots then 
            (let n = snd (the (hd roots));
                 new_eqcs = zip_lists n (map args eqc')
             in (if Ball (set new_eqcs) (\<lambda> eqc. uniq_list (map sort_of eqc)) then simplify_mp_main (new_eqcs @ mp) mpout else None)) 
          else None)))"
  by pat_completeness auto

termination 
proof (relation "measures [\<lambda> mp. sum_list (map (\<lambda> eqc. sum_list (map size eqc)) (fst mp)), length o fst]", force, force, force, goal_cases)
  case (1 eqc mp mpout eqc' roots n new_eqcs)
  note new = 1(7)
  from 1 obtain r where "set roots = {r}" unfolding is_singleton_list2 by auto
  with 1(4,6) obtain f where roots: "set roots = {Some (f,n)}" 
    by (cases roots; cases r, auto)
  {
    fix t
    assume "t \<in> set eqc'" 
    with 1(3-4) obtain g s ts where t: "t = Fun (g,s) ts" and rt: "Some (g,length ts) \<in> set roots" 
      by (cases t; force simp: aroot_def o_def)
    hence len: "length (args t) = n" "root t = Some ((f,s),n)" using roots by auto
    hence "size t = Suc (sum_list (map size (args t)) + n)" unfolding t 
      by (simp add: size_list_conv_sum_list)
    also have "sum_list (map size (args t)) = (\<Sum>i\<leftarrow>[0..<n]. size (args t ! i))" 
      by (rule arg_cong[of _ _ sum_list], rule nth_equalityI, insert len, auto)
    finally have "size t = Suc n + (\<Sum>i\<leftarrow>[0..<n]. size (args t ! i))" by simp
    note len(1) this
  } note root_terms = this

  let ?sum = "\<lambda> eqc. sum_list (map size eqc)" 
  define common where "common = (\<Sum>t\<leftarrow>eqc'. \<Sum>i\<leftarrow>[0..<n]. size (args t ! i))" 
  have "sum_list (map ?sum new_eqcs) = 
     sum_list (map ?sum (map (\<lambda>i. map (\<lambda>xs. xs ! i) (map args eqc')) [0..<n]))" 
    unfolding new by (subst zip_lists, insert root_terms(1), auto)
  also have "\<dots> = (\<Sum>i\<leftarrow>[0..<n]. (\<Sum>t\<leftarrow>eqc'. size (args t ! i)))" 
    by (simp add: size_list_conv_sum_list o_def sum_list_addf sum_list_triv) 
  also have "(\<Sum>i\<leftarrow>[0..<n]. (\<Sum>t\<leftarrow>eqc'. size (args t ! i))) = common" 
    unfolding common_def
    by (induct eqc', auto simp: sum_list_addf)
  finally have lhs: "sum_list (map ?sum new_eqcs) = common" .

  define sn where "sn = Suc n" 
  have "?sum eqc' = (\<Sum>t\<leftarrow>eqc'. Suc n + (\<Sum>i\<leftarrow>[0..<n]. size (args t ! i)))" 
    by (subst map_cong[OF refl], subst root_terms(2), auto)
  also have "\<dots> = common + length eqc' * Suc n" 
    unfolding sn_def[symmetric] common_def by (simp add: sum_list_addf sum_list_triv)
  finally have rhs: "?sum eqc' = common + length eqc' * Suc n" by simp

  from 1 have "eqc' \<noteq> []" unfolding is_singleton_list2 by auto
  hence "sum_list (map ?sum new_eqcs) < ?sum eqc'" 
    unfolding lhs rhs by simp
  also have "\<dots> \<le> ?sum eqc" unfolding \<open>eqc' = remdups eqc\<close>
    by (metis sum.set_conv_list sum_le_sum_list_nat)
  finally show ?case by simp
qed

definition "simplify_mp mp = simplify_mp_main mp []" 

(* simplify all matching problems and also detect empty mps *)
primrec simplify_pp :: "('f,'s)simple_pat_problem_slist \<Rightarrow> ('f,'s)simple_pat_problem_slist option" where
  "simplify_pp [] = Some []" 
| "simplify_pp (mp # p) = (case 
     simplify_mp mp of 
       None \<Rightarrow> simplify_pp p
     | Some mp' \<Rightarrow> if mp' = [] then None else map_option (Cons mp') (simplify_pp p))" 

fun simplify_tpp :: "('f,'s)tagged_simple_pat_problem_slist \<Rightarrow> ('f,'s)tagged_simple_pat_problem_slist option" where
  "simplify_tpp (True, p) = Some (True, p)" 
| "simplify_tpp (False, p) = map_option (Pair True) (simplify_pp p)"

definition s\<tau>c :: "nat \<Rightarrow> nat \<times> 's \<Rightarrow> 'f \<times> 's list \<Rightarrow> ('f \<times> 's,nat \<times> 's)subst" where 
  "s\<tau>c n x = (\<lambda>(f,ss). subst x (Fun (f,snd x) (map Var (zip [n ..< n + length ss] ss))))"

definition s\<tau>s_list :: "nat \<Rightarrow> nat \<times> 's \<Rightarrow> ('f \<times> 's,nat \<times> 's)subst list" where
  "s\<tau>s_list n x = map (s\<tau>c n x) (Cl (snd x))"

lemma add_sort_\<tau>c: assumes "f : ss \<rightarrow> snd x in C"
  "t : \<iota> in \<T>(C,\<V>)" 
  shows "add_sort (t \<cdot> \<tau>c n x (f,ss)) = add_sort t \<cdot> s\<tau>c n x (f,ss)"
proof -
  from assms(2) 
  have "add_sort (t \<cdot> \<tau>c n x (f,ss)) = add_sort t \<cdot> s\<tau>c n x (f,ss) \<and> sort_of (add_sort t \<cdot> s\<tau>c n x (f,ss)) = sort_of (add_sort t)" 
  proof (induct)
    case (Fun g ts)
    thus ?case apply (auto simp: o_def) 
       apply (smt (verit, best) length_map list_all2_conv_all_nth list_eq_iff_nth_eq nth_map)
      by (smt (verit, del_insts) in_set_conv_nth list_all2_conv_all_nth)
  next
    case (Var y s)
    thus ?case using assms(1) apply (cases x, auto simp: s\<tau>c_def \<tau>c_def subst_def o_def split: prod.splits)
      by (metis (no_types, lifting) ext enumerate_eq_zip fun_hastype_def map_snd_enumerate option.sel
          sort_of.simps(2) surjective_pairing)
  qed
  thus ?thesis by auto
qed

definition inst_list :: "nat \<Rightarrow> nat \<times> 's \<Rightarrow> ('f,'s)simple_pat_problem_slist \<Rightarrow> ('f,'s)simple_pat_problem_slist list" 
  where "inst_list n x p = map (\<lambda> \<tau>. map (map (map (\<lambda>t. t \<cdot> \<tau>))) p) (s\<tau>s_list n x)" 

definition full_step :: "nat \<Rightarrow> ('f,'s)tagged_simple_pat_problem_slist \<Rightarrow> ('f,'s)tagged_simple_pat_problem_slist list + (nat \<times> 's) list list list" where 
  "full_step n p = (case simplify_tpp p of None \<Rightarrow> Inl []
     | Some (True,p') \<Rightarrow> (case large_sort_impl p' of 
      Some p2 \<Rightarrow> (Inl [(True,p2)])       
     | None \<Rightarrow> (case search_fun_pp p' of
     None \<Rightarrow> Inr (map (map (map the_Var)) p')
   | Some (p1,mp,(mp1,eqc,(eqc1,t,eqc2),mp2),p2) \<Rightarrow> 
       let x = the (find is_Var eqc)
       in if mp = [[t,x]] \<or> mp = [[x,t]] then Inl (map (Pair False) (inst_list n (the_Var x) p'))
       else let eqn = eqc1 @ eqc2; mpn = (if length_gt_1 eqn then eqn # mp1 @ mp2 else mp1 @ mp2) 
          in Inl ((True, mpn # p1 @ p2) 
           # map (Pair False) (inst_list n (the_Var x) ([[x,t]] # p1 @ p2))))))"

definition fidl_encoder :: "('x \<times> 's) list list list \<Rightarrow> ('x,'s) fidl_input" where
  "fidl_encoder p = (let vars = remdups (concat (concat p))
     in (map (\<lambda> x. (x, int (cd_sort (snd x)))) vars, map (List.maps (\<lambda> eqc. zip eqc (tl eqc))) p))"

context
  fixes fidl_solver :: "(nat,'s) fidl_input \<Rightarrow> bool" 
begin

definition "fvf_solver fvf = (\<not> fidl_solver (bounds_list (cd_sort \<circ> snd) fvf, dist_pairs_list fvf))" 

partial_function (tailrec) fcf_solver_loop where
  "fcf_solver_loop n P = (case P of [] \<Rightarrow> True
     | p # ps \<Rightarrow> (case full_step n p of 
     Inl ps1 \<Rightarrow> fcf_solver_loop (n + m) (ps1 @ ps)
   | Inr fvf \<Rightarrow> if fvf_solver fvf then fcf_solver_loop n ps
          else False))"

abbreviation add1 where "add1 \<equiv> map add_sort" 
abbreviation add2 where "add2 \<equiv> map add1" 
abbreviation add3 where "add3 \<equiv> map add2" 

definition "fcf_solver_alg n p = fcf_solver_loop n [(False, add3 p)]" 
end

lemma mset2_mset2'_set2[simp]: "mset2 (mset2' mp) = set2 mp" 
  by (induct mp, auto)

lemma mset3_mset3'_set3[simp]: "mset3 (mset3' p) = set3 p"
  apply (induct p)
   apply force
  subgoal for mp p using mset2_mset2'_set2[of mp] by simp
  done

end

context pattern_completeness_context_with_assms
begin

lemma mp_steps_cong: assumes "finite_constructor_form_pat (mset3 (add_mset mp p))" 
  shows "(\<rightarrow>\<^sub>s\<^sub>s)\<^sup>*\<^sup>* mp mp' \<Longrightarrow>
  (add_mset (add_mset mp p) P, add_mset (add_mset mp' p) P) \<in> (\<Rrightarrow>\<^sub>s\<^sub>s)\<^sup>*
  \<and> finite_constructor_form_pat (mset3 (add_mset mp' p))"
proof (induct rule: rtranclp_induct)
  case (step mp1 mp2)  
  from spp_simp[OF step(2), of p]
  have p_step: "add_mset mp1 p \<Rightarrow>\<^sub>s\<^sub>s {#add_mset mp2 p#}" .
  from spp_step_ms[OF p_step] step(3)
  have fin: "finite_constructor_form_pat (mset3 (add_mset mp2 p))" by auto
  from spp_non_det_step[OF p_step] step(3)
  have P_step: "(add_mset (add_mset mp1 p) P, {#add_mset mp2 p#} + P) \<in> \<Rrightarrow>\<^sub>s\<^sub>s" by auto
  with fin step(3) show ?case by auto
qed (insert assms, auto)

definition "simplified_mp mp = (Ball (set mp) (\<lambda> eqc. length eqc > 1 \<and> (\<exists> t \<in> set eqc. is_Var t) \<and> distinct eqc))" 

definition "simplified_pp p = (Ball (set p) (\<lambda> mp. simplified_mp mp \<and> mp \<noteq> []))" 

lemma simplify_mp_main: assumes "rel_smp mpl (mpsl @ mpsout) mpm"  
  and "res = simplify_mp_main mpsl mpsout" 
  and "Ball (set mpsout) prop" 
  and "tvars_smp (set2 mpl) \<subseteq> V" 
  and "prop = (\<lambda> eqc. length eqc > 1 \<and> (\<exists> t \<in> set eqc. is_Var t) \<and> distinct eqc)" 
shows "res = Some mpsl' \<Longrightarrow> \<exists> mpl' mpm'. rel_smp mpl' mpsl' mpm' \<and> (\<rightarrow>\<^sub>s\<^sub>s)\<^sup>*\<^sup>* mpm mpm' 
             \<and> Ball (set mpsl') prop \<and> tvars_smp (set2 mpl') \<subseteq> V" 
    "res = None \<Longrightarrow> \<exists> mpm'. (\<rightarrow>\<^sub>s\<^sub>s)\<^sup>*\<^sup>* mpm mpm' \<and> smp_fail_ms mpm'" 
  using assms(1-4)
proof (atomize(full), induction mpsl mpsout arbitrary: mpl mpm rule: simplify_mp_main.induct)
  case (1 mpout)
  then show ?case unfolding rel_smp_def by auto
next
  case (2 seqc mps mpsout mpl mpm)
  note IH = "2.IH"
  note res = "2.prems"(2)[unfolded simplify_mp_main.simps(2)] 
  note rel = rel_smpD[OF "2.prems"(1)]
  note props = "2.prems"(3)
  from rel obtain eqc mpl' where mpl: "mpl = eqc # mpl'" and seqc': "seqc = map add_sort eqc" 
    and mps: "mps @ mpsout = map (map add_sort) mpl'" by (cases mpl, auto)
  from rel have fin: "finite_constructor_form_mp (set2 mpl)" by auto
  from fin[unfolded mpl finite_constructor_form_mp_def] obtain t eq where
    eqc: "eqc = t # eq" by (cases eqc, auto)
  with seqc' have seqc: "seqc = add_sort t # map add_sort eq" by auto
  from fin[unfolded mpl eqc finite_constructor_form_mp_def] obtain s where 
    "t : s in \<T>(C, \<V> |` SS)" by auto
  hence ts: "t : s in \<T>(C, \<V>)" by (rule typed_restrict_imp_typed)
  from add_sort[OF ts] 
  have "sort_of (add_sort t) = s" by simp  
  hence sort: "sort_of (hd seqc) = s" unfolding seqc by simp
  note res = res[unfolded sort]
  have tvars: "tvars_smp (set2 mpl') \<subseteq> V" "tvars_smp ({set eqc}) \<subseteq> V" using 2(7) unfolding mpl by auto
  let ?delcond = "is_singleton_list seqc \<or> cd_sort s = 1" 
  show ?case
  proof (cases ?delcond)
    case True
    with res have res: "res = simplify_mp_main mps mpsout" by simp
    from True have "is_singleton_list seqc \<or> cd_sort (sort_of (hd seqc)) = 1" 
      using sort by auto
    note IH = IH(1)[OF this]
    from True have steps: "(\<rightarrow>\<^sub>s\<^sub>s)\<^sup>*\<^sup>* mpm (mset (map mset mpl'))"
    proof 
      assume cd: "cd_sort s = 1" 
      from rel(5)[unfolded mpl eqc] 
      have mpm: "mpm = add_mset (add_mset t (mset eq)) (mset2' mpl')" by auto
      show ?thesis unfolding mpm
        apply (rule r_into_rtranclp)
        apply (rule smp_triv_sort[OF ts cd])
        done
    next
      assume "is_singleton_list seqc" 
      from this[unfolded is_singleton_list2] seqc eqc obtain st where "set (map add_sort eqc) = {st}" by auto
      from arg_cong[OF this, of "(`) remove_sort", unfolded set_map image_comp o_def]
      have single: "is_singleton_list eqc" by (simp add: is_singleton_list2)
      from rel[unfolded mpl] have mpm: "mpm = add_mset (mset eqc) (mset2' mpl')" by auto
      define mp where "mp = mset2' mpl'" 
      from single show ?thesis unfolding mpm mp_def[symmetric]
      proof (induct eqc rule: is_singleton_list.induct)
        case (1 x)
        show ?case by (rule r_into_rtranclp, unfold mset.simps, rule smp_singleton)
      next
        case (2 x y xs)
        from 2(2) have y: "y = x" and single: "is_singleton_list (x # xs)" by auto
        show ?case unfolding y using 2(1)[OF single] smp_dup[of x]
          by (metis converse_rtranclp_into_rtranclp mset.simps(2))
      qed auto 
    qed
    have rel: "rel_smp mpl' (mps @ mpsout) (mset2' mpl')" 
      using rel unfolding rel_smp_def mpl seqc' by (simp add: finite_constructor_form_mp_def) 
    from IH[OF rel res _ tvars(1)] props steps show ?thesis by (meson rtranclp_trans)
  next
    case False
    hence "?delcond = False" by auto  
    note res = res[unfolded this if_False]
    from False sort have "\<not> (is_singleton_list seqc \<or> cd_sort (sort_of (hd seqc)) = 1)" by auto
    note IH = IH(2-)[OF this]
    define seqc1 where "seqc1 = remdups seqc" 
    note IH = IH[OF seqc1_def]
    define xs :: "('f, nat \<times> 's) term list" where "xs = []" 
    from "2.prems"(1)[unfolded mpl seqc'] mps 
    have "rel_smp ((xs @ eqc) # mpl') ((add1 xs @ add1 eqc) # add2 mpl') mpm" 
      by (auto simp: xs_def)
    hence "\<exists> mpm'. rel_smp ((xs @ remdups eqc) # mpl') ((add1 xs @ remdups (add1 eqc)) # add2 mpl') mpm' \<and> (\<rightarrow>\<^sub>s\<^sub>s)\<^sup>*\<^sup>* mpm mpm'" 
    proof (induct eqc arbitrary: xs mpm)
      case Nil
      thus ?case by auto
    next
      case (Cons x eqc xs mpm) 
      hence rel: "rel_smp ((xs @ x # eqc) # mpl') ((add1 xs @ add1 (x # eqc)) # add2 mpl') mpm" by auto
      show ?case
      proof (cases "x \<in> set eqc")
        case True
        hence rem: "remdups (x # eqc) = remdups eqc" "remdups (add1 (x # eqc)) = remdups (add1 eqc)" by auto
        from True have "eqc \<noteq> []" by auto
        with rel have rel': "rel_smp ((xs @ eqc) # mpl') ((add1 xs @ add1 eqc) # add2 mpl') (add_mset (mset (xs @ eqc)) (mpm - mset2' [xs @ x # eqc]))" 
          by (auto simp: rel_smp_def finite_constructor_form_mp_def)
        from True obtain eqc' where eqc: "mset eqc = add_mset x eqc'"
          by (metis insert_DiffM set_mset_mset)
        from rel_smpD(5)[OF rel] eqc have mpm: "mpm = add_mset (add_mset x (add_mset x (mset xs + eqc'))) (mset2' mpl')" 
          by auto
        have "mpm \<rightarrow>\<^sub>s\<^sub>s add_mset (add_mset x (mset xs + eqc')) (mset2' mpl')" 
          using smp_dup[of x "mset xs + eqc'" "mset2' mpl'", folded mpm] .
        hence step: "mpm \<rightarrow>\<^sub>s\<^sub>s add_mset (mset (xs @ eqc)) (mpm - mset (map mset [xs @ x # eqc]))"
          using eqc mpm by auto
        show ?thesis unfolding rem using Cons(1)[OF rel'] unfolding rem using step by auto
      next
        case False
        with inj_add_sort[unfolded inj_def] 
        have rem: "remdups (x # eqc) = x # remdups eqc" "remdups (add1 (x # eqc)) = add_sort x # remdups (add1 eqc)" 
          by auto
        from rel have rel: "rel_smp (((xs @ [x]) @ eqc) # mpl') ((add1 (xs @ [x]) @ add1 eqc) # add2 mpl') mpm" 
          unfolding rel_def by auto              
        show ?thesis unfolding rem using Cons(1)[OF rel] by auto
      qed
    qed
    from this[unfolded xs_def, folded seqc', folded seqc1_def] 
    obtain mpm1 eqc1 where
      rel: "rel_smp (eqc1 # mpl') (seqc1 # map (map add_sort) mpl') mpm1" and
      steps1: "(\<rightarrow>\<^sub>s\<^sub>s)\<^sup>*\<^sup>* mpm mpm1" 
      by auto
    define mpl1 where "mpl1 = take (length mps) mpl'" 
    define mpl2 where "mpl2 = drop (length mps) mpl'" 
    have mpl': "mpl' = mpl1 @ mpl2" unfolding mpl1_def mpl2_def by auto
    from mps have mps: "mps = add2 mpl1" and mpsout: "mpsout = add2 mpl2" 
      unfolding mpl1_def mpl2_def 
      by (force simp add: append_eq_conv_conj take_map) (metis append_eq_conv_conj drop_map mps)
    from rel[unfolded mpl']
    have rel_out: "rel_smp (mpl1 @ eqc1 # mpl2) (mps @ seqc1 # mpsout) mpm1" unfolding mps mpsout 
      by (auto simp: rel_smp_def)

    define roots where "roots = map aroot seqc1" 
    note IH = IH[OF roots_def]
    note res = res[folded seqc1_def, unfolded Let_def, folded roots_def]
    show ?thesis
    proof (cases "None \<in> set roots")
      case True
      hence "(None \<in> set roots) = True" by auto
      note res = res[unfolded this if_True]
      note IH = IH(1)[OF True]
      have prop1: "prop seqc1" unfolding assms(5)
      proof (intro conjI)
        from True obtain s where s: "s \<in> set seqc" and root: "aroot s = None" 
          unfolding roots_def seqc1_def by auto
        from root have "is_Var s" unfolding aroot_def by (cases s, auto)
        with s show "Bex (set seqc1) is_Var" by (auto simp: seqc1_def)
        from False have "\<not> is_singleton_list seqc" by auto
        from this[unfolded is_singleton_list2] 
        have no_single: "set seqc \<noteq> {s}" by auto
        with s obtain t where st: "{s,t} \<subseteq> set seqc1" and "s \<noteq> t"
          unfolding seqc1_def by auto
        thus "1 < length seqc1" by (cases seqc1; cases "tl seqc1"; auto)
        show "distinct seqc1" unfolding seqc1_def by auto
      qed
      show ?thesis
      proof (cases "\<forall>t\<in>set seqc1. \<forall>s\<in>set seqc1. conflicts (remove_sort s) (remove_sort t) \<noteq> None")
        case False
        with res have res: "res = None" by argo
        from False obtain ss st where ss: "ss \<in> set seqc1" and st: "st \<in> set seqc1" 
          and clash: "Conflict_Clash (remove_sort ss) (remove_sort st)" by auto
        from rel_smpD[OF rel] obtain mpm2 where
          seqc1: "seqc1 = map add_sort eqc1" and mpm1: "mpm1 = add_mset (mset eqc1) mpm2"
          by auto
        from ss st obtain s t where s: "s \<in> set eqc1" and t: "t \<in> set eqc1" and ss: "ss = add_sort s" and 
          st: "st = add_sort t" 
          unfolding seqc1 by auto
        from clash[unfolded ss st] have clash: "Conflict_Clash s t" by auto
        hence st: "s \<noteq> t" by auto
        with s t have "s \<in># mset eqc1" "t \<in># mset eqc1" by auto
        from smp_clash[OF clash this] mpm1 have "smp_fail_ms mpm1" by auto
        with res steps1 show ?thesis by auto
      next
        case True
        with res have res: "res = simplify_mp_main mps (seqc1 # mpsout)" by auto  
        {
          fix t
          assume "t \<in> set eqc1" 
          with rel[unfolded rel_smp_def] have "add_sort t \<in> set seqc1" by auto
          hence "add_sort t \<in> set seqc" unfolding seqc1_def by auto
          hence "t \<in> set eqc" unfolding seqc' by auto
        }
        hence tvars: "tvars_smp (set2 (mpl1 @ eqc1 # mpl2)) \<subseteq> V" using 2(7) unfolding mpl mpl' by auto
        from props prop1 have "\<forall>eq\<in>set (seqc1 # mpsout). prop eq" by auto
        from IH[OF True rel_out res this tvars] steps1 props prop1 show ?thesis
          by (meson rtranclp_trans)
      qed
    next
      case roots: False
      hence "(None \<in> set roots) = False" by auto
      note res = res[unfolded this if_False]
      note IH = IH(2)[OF roots]
      from rel_smpD[OF rel] 
      have fin: "finite_constructor_form_mp (set2 (eqc1 # mpl'))" 
        and eqc1: "set eqc1 \<in> mset2 mpm1"
        and seqc1: "seqc1 = add1 eqc1" by auto
      show ?thesis
      proof (cases "is_singleton_list roots")
        case False
        with res have res: "res = None" by auto
        from False[unfolded is_singleton_list2] have no_sing: "\<nexists>x. set roots = {x}" by auto
        from fin[unfolded finite_constructor_form_mp_def] 
        have ne: "eqc1 \<noteq> []" by auto
        from ne seqc1 have "set roots \<noteq> {}" unfolding roots_def by auto
        then obtain f where f: "f \<in> set roots" by fastforce
        with no_sing obtain g where "g \<in> set roots - {f}" by blast
        with f have "{f,g} \<subseteq> set roots" and "f \<noteq> g" by auto
        with roots obtain f g where fg: "{Some f, Some g} \<subseteq> set roots" and diff: "f \<noteq> g" 
          by (cases f; cases g; auto)
        from fg[unfolded roots_def seqc1 map_map o_def aroot]
        obtain s t where st: "s \<in> set eqc1" "t \<in> set eqc1" and rt: "root s = Some f" "root t = Some g" by auto
        have "Conflict_Clash s t" using rt diff by (cases s; cases t, auto simp: conflicts.simps)
        from smp_clash[OF this st eqc1]
        have "smp_fail_ms mpm1" .
        with steps1 res show ?thesis by auto
      next
        case True
        from True[unfolded is_singleton_list2] obtain f where "set roots = {f}" by auto
        with roots obtain f n where rt: "set roots = {Some (f,n)}" by (cases f, auto)
        have "set roots = root ` set eqc1" unfolding roots_def seqc1 by auto
        from this[unfolded rt] 
        have rt': "t \<in># mset eqc1 \<Longrightarrow> root t = Some (f, n)" for t by auto
        have snd: "snd (the (hd roots)) = n" using rt by (cases roots, auto)
        define new_eqs where "new_eqs = zip_lists n (map args seqc1)" 
        note IH = IH[OF True snd[symmetric] new_eqs_def]
        define new_plain where "new_plain = map (\<lambda>i. map (\<lambda>x. args x ! i) eqc1) [0..<n]" 
        have "new_eqs = map (\<lambda>i. map (\<lambda>xs. xs ! i) (map args seqc1)) [0..<n]" 
          unfolding new_eqs_def 
          apply (rule zip_lists) 
          apply (clarsimp simp add: seqc1)
          subgoal for t using rt'[of t] by (cases t, auto)
          done
        also have "\<dots> = map (\<lambda>i. map (\<lambda>x. args (add_sort x) ! i) eqc1) [0..<n]" 
          unfolding seqc1 by (simp add: o_def)
        also have "\<dots> = add2 (map (\<lambda>i. map (\<lambda>x. args x ! i) eqc1) [0..<n])" unfolding map_map o_def
          apply (rule map_cong[OF refl], rule map_cong[OF refl])
          subgoal for i t
            using rt'[of t] by (cases t, auto)
          done
        finally have new_eqs: "new_eqs = add2 new_plain" unfolding new_plain_def .

        from rel_smpD(5)[OF rel]
        have mpm1: "mpm1 = add_mset (mset eqc1) (mset2' mpl')" by auto

        from True have "(is_singleton_list roots) = True" by auto
        note res = res[unfolded this if_True, unfolded snd]
        note decomp = smp_decomp smp_decomp_fail
        note decomp = decomp[OF rt', of "mset eqc1", simplified] 
        have eq: "mset2' new_plain = {#{#args t ! i. t \<in># mset eqc1#}. i \<in># mset_set {0..<n}#}" 
          unfolding mset_map mset_upt image_mset.compositionality o_def new_plain_def by blast 
        let ?uniq = "\<forall>eqc\<in>set new_eqs. uniq_list (map sort_of eqc)" 
        have "?uniq \<longleftrightarrow> (\<forall>eqc\<in>set new_plain. UNIQ {sort_of (add_sort x) |. x \<in> set eqc})" 
          unfolding uniq_list new_eqs set_map by (auto simp: image_comp)
        also have "\<dots> \<longleftrightarrow> (\<forall> eqc \<in> set new_plain. UNIQ (\<T>(C,\<V>) ` set eqc))"
        proof (intro ball_cong refl arg_cong[of _ _ UNIQ])
          fix eqc
          assume "eqc \<in> set new_plain" 
          from this[unfolded new_plain_def, simplified] obtain i where i: "i < n" 
            and eqc: "eqc = map (\<lambda>xa. args xa ! i) eqc1" by auto
          have "UNIQ {sort_of (add_sort x) |. x \<in> set eqc} = UNIQ {Some (sort_of (add_sort x)) |. x \<in> set eqc}" 
            unfolding Uniq_def by auto
          also have "{Some (sort_of (add_sort x)) |. x \<in> set eqc} = \<T>(C,\<V>) ` set eqc" 
          proof (intro image_cong refl)
            fix ti 
            assume "ti \<in> set eqc" 
            from this[unfolded eqc] obtain t where t: "t \<in> set eqc1" and ti: "ti = args t ! i" by auto
            from fin t obtain s where "t : s in \<T>(C, \<V> |` SS)" unfolding finite_constructor_form_mp_def by auto
            hence typed: "t : s in \<T>(C, \<V>)" by (rule typed_restrict_imp_typed)
            from rt'[of t] t i obtain ts where tf: "t = Fun f ts" and tis: "ti \<in> set ts" 
              unfolding ti by (cases t, auto)
            from typed[unfolded tf] tis obtain si where typed: "ti : si in \<T>(C, \<V>)"
              by (meson Fun_in_dom_imp_arg_in_dom in_dom_iff_ex_type)
            from add_sort[OF this] have "sort_of (add_sort ti) = si" by auto
            with typed ti t i show "Some (sort_of (add_sort ti)) = \<T>(C,\<V>) ti" 
              by (force simp: hastype_def eqc)
          qed
          finally show "UNIQ {sort_of (add_sort x) |. x \<in> set eqc} = UNIQ (\<T>(C,\<V>) ` set eqc)" .
        qed
        finally have uniq: "(\<forall>eqc\<in>set new_eqs. uniq_list (map sort_of eqc)) 
               = (\<forall>eqc\<in>set new_plain. UNIQ (\<T>(C,\<V>) ` set eqc))" .
        show ?thesis
        proof (cases ?uniq)
          case True
          with res 
          have res: "res = simplify_mp_main (new_eqs @ mps) mpsout"  
            by (auto simp: new_eqs_def)
          from True have uniq: "eq \<in># mset (map mset new_plain) \<Longrightarrow> UNIQ (\<T>(C,\<V>) ` set_mset eq)" for eq
            unfolding uniq by auto            
          note IH = IH[OF True _ res]
          from decomp(1)[OF eq uniq] 
          have step2: "mpm1 \<rightarrow>\<^sub>s\<^sub>s mset2' new_plain + mset2' mpl'" by (auto simp: mpm1)
          from rel_smpD[OF "2.prems"(1)]
          have fin: "finite_constructor_form_pat (mset3 {#mpm#})" 
            by (auto simp: finite_constructor_form_pat_def)
          from steps1 step2 
          have steps2: "(\<rightarrow>\<^sub>s\<^sub>s)\<^sup>*\<^sup>* mpm (mset2' (new_plain @ mpl'))" by auto
          from mp_steps_cong[OF fin steps2, of "{#}", THEN conjunct2]
          have fin': "finite_constructor_form_mp (set2 (new_plain @ mpl'))" 
            by (auto simp: finite_constructor_form_pat_def image_Un image_comp)
          hence rel_new: "rel_smp (new_plain @ mpl1 @ mpl2) ((new_eqs @ mps) @ mpsout) 
            (mset2' (new_plain @ mpl'))" 
            unfolding mps new_eqs seqc1 mpsout rel_smp_def mpl' by auto
          have "tvars_smp (set2 (mpl1 @ mpl2)) \<subseteq> V" using mpl' tvars by auto
          moreover have "tvars_smp (set2 new_plain) \<subseteq> V" unfolding new_plain_def
          proof (clarsimp, goal_cases)
            case (1 x \<iota> i t) 
            hence mem: "(x,\<iota>) \<in> vars t" using rt'[of t] by (cases t, auto) 
            from \<open>t \<in> set eqc1\<close> 
            have "add_sort t \<in> set (add1 eqc1)" by auto
            also have "set (add1 eqc1) = set (add1 eqc)" 
              unfolding seqc1[symmetric] seqc1_def set_remdups seqc' by simp
            finally have "t \<in> set eqc" by auto
            with mem tvars(2) show "(x,\<iota>) \<in> V" by auto
          qed
          ultimately have tvars: "tvars_smp (set2 (new_plain @ mpl1 @ mpl2)) \<subseteq> V" by auto
          from IH[OF rel_new _ tvars] props steps2 show ?thesis
            by (metis (no_types, lifting)  rtranclp_trans)
        next
          case False
          with res have res: "res = None" by (auto simp: new_eqs_def)
          from False[unfolded uniq, unfolded new_plain_def, simplified]
          obtain i where i: "i < n" and uniq: "\<not> UNIQ (\<T>(C,\<V>) ` {args t ! i |. t \<in> set eqc1})" by auto
          from decomp(2)[OF i uniq] have "smp_fail_ms mpm1" unfolding mpm1 by auto
          with steps1 res show ?thesis by auto
        qed
      qed
    qed
  qed
qed

lemma sorts_of_subterm: "t \<unrhd> a \<Longrightarrow> a : s in \<T>(C,\<V>) \<Longrightarrow> s \<in> sorts_of (add_sort t)" 
proof (induct rule: supteq.induct)
  case (refl t)
  then show ?case using add_sort[of t s] by (cases t; force)
next
  case (subt u ss t f)
  then show ?case by auto
qed 

lemma vars_term_add_sort[simp]: "vars_term (add_sort t) = vars_term t" 
  by (induct t, auto)

lemma eroot_add_sort: assumes "t : \<iota> in \<T>(C,\<V>)"
  shows "eroot (add_sort t) = map_sum (map_prod (\<lambda> f. (f,\<iota>)) id) id (eroot t)" 
  using assms add_sort[OF assms]
  by (cases t, auto)

lemma large_sort_impl: assumes "large_sort_impl (add3 p) = Some ap'" 
  and fin: "finite_constructor_form_pat (set3 p)" 
  and simpl: "simplified_pp p" 
  shows "\<exists> p'. mset3' p \<Rightarrow>\<^sub>s\<^sub>s {# mset3' p' #} \<and> ap' = add3 p' \<and> set p' \<subseteq> set p \<and> length p' \<le> length p" 
proof -
  from assms(1)[unfolded large_sort_impl_def Let_def]
  obtain bef s aft sorts where 
    "extract_option (large_sort_impl_main (add3 p)) sorts = Some (bef, s, ap', aft)" 
    and sorts: "sorts = remdups (map sort_of (concat (concat (add3 p))))" 
    by auto
  from extract_option_Some[OF this(1)] 
  have large: "large_sort_impl_main (add3 p) s = Some ap'" and s: "s \<in> set sorts" by auto
  {
    from s[unfolded sorts, simplified] obtain mp eqc t where
      *: "mp \<in> set p" "eqc \<in> set mp" "t \<in> set eqc" and st: "s = sort_of (add_sort t)" by blast
    from * fin[unfolded finite_constructor_form_pat_def finite_constructor_form_mp_def]
    obtain \<iota> where fin: "finite_sort C \<iota>" and t: "t : \<iota> in \<T>(C,\<V> |` SS)" by fastforce
    hence iota: "\<iota> \<in> S" by (metis typed_imp_S)
    with s st t have "s = \<iota>"
      by (meson add_sort typed_restrict_imp_typed)
    with fin iota have "s \<in> S" "finite_sort C s" by auto
  } note s = this
    
  
  define confl where "confl = (\<lambda>mp :: ('f \<times> 's, nat \<times> 's) term list list. \<exists>eqc\<in>set mp. sort_of (hd eqc) = s)" 
  obtain del keep where part1: "partition (confl o add2) p = (del, keep)" by auto
  hence part2: "partition confl (add3 p) = (map add2 del, map add2 keep)"
    unfolding partition_filter_conv by (simp add: comp_assoc filter_map)
  from large[unfolded large_sort_impl_main_def, folded confl_def, unfolded Let_def part2 split]
  have card: "length del < cd_sort s" and del: "del \<noteq> []" and 
    keep: "(\<forall>mp\<in>set (add3 keep). \<forall>eq\<in>set mp. \<forall>t\<in>set eq. \<forall>x\<in>set (vars_term_list t). snd x \<noteq> s)" 
    and ap': "ap' = (add3 keep)" 
    by (auto split: if_splits)
  {
    fix i
    assume i: "i < length del" 
    let ?mp = "del ! i" 
    from i have "?mp \<in> set del" by auto
    with part1 have confl: "confl (add2 ?mp)" and "?mp \<in> set p" by auto
    with simpl[unfolded simplified_pp_def] fin[unfolded finite_constructor_form_pat_def]
    have simpl: "simplified_mp ?mp" and fin: "finite_constructor_form_mp (set2 ?mp)" by auto
    from confl[unfolded confl_def]
    obtain eqc where eqc: "eqc \<in> set ?mp" and sort: "sort_of (hd (add1 eqc)) = s" by auto
    from simpl[unfolded simplified_mp_def, rule_format, OF eqc] obtain x
      where len: "1 < length eqc" and var: "Var x \<in> set eqc" and dist: "distinct eqc" by auto
    from fin[unfolded finite_constructor_form_mp_def, rule_format, of "set eqc"] eqc 
    obtain \<iota> where same_sort: "\<And> t. t\<in> set eqc \<Longrightarrow> t : \<iota> in \<T>(C,\<V> |` SS)" by auto
    from len have "hd eqc \<in> set eqc" and hd: "hd (add1 eqc) = add_sort (hd eqc)" by (cases eqc, auto)+
    from same_sort[OF this(1)] sort have "\<iota> = s" unfolding hd
      by (metis add_sort typed_restrict_imp_typed) 
    note same_sort = same_sort[unfolded this]
    from split_list[OF var] obtain bef aft where split: "eqc = bef @ Var x # aft" by auto
    with len obtain t where "t \<in> set bef \<union> set aft" by (cases bef; cases aft, auto)
    with split dist have xt: "Var x \<noteq> t" "t \<in> set eqc" by auto
    from same_sort[OF var] have xs: "snd x = s"
      by (simp add: hastype_restrict)
    from same_sort[OF xt(2)] have sorted: "t : s in \<T>(C,\<V>)" 
      by (metis typed_restrict_imp_typed)
    have "\<exists> x t eqc. {Var x, t} \<subseteq> set eqc \<and> Var x \<noteq> t \<and> eqc \<in> set ?mp \<and> snd x = s \<and> t : s in \<T>(C,\<V>)" 
      by (rule exI[of _ x], rule exI[of _ t], rule exI[of _ eqc], insert xt var eqc xs sorted, auto)
  }
  hence "\<forall> i. \<exists> x t eqc. i < length del \<longrightarrow> {Var x, t} \<subseteq> set eqc \<and> Var x \<noteq> t \<and> eqc \<in> set (del ! i) \<and> snd x = s \<and> t : s in \<T>(C,\<V>)" 
    by blast
  from choice[OF this] obtain x where 
    "\<forall> i. \<exists> t eqc. i < length del \<longrightarrow> {Var (x i), t} \<subseteq> set eqc \<and> Var (x i) \<noteq> t \<and> eqc \<in> set (del ! i) \<and> snd (x i) = s \<and> t : s in \<T>(C,\<V>)"
    by blast
  from choice[OF this] obtain t where 
    "\<forall> i. \<exists> eqc. i < length del \<longrightarrow> {Var (x i), t i} \<subseteq> set eqc \<and> Var (x i) \<noteq> t i \<and> eqc \<in> set (del ! i) \<and> snd (x i) = s \<and> t i : s in \<T>(C,\<V>)"
    by blast
  from choice[OF this] obtain eqc where 
    xte: "\<And> i.  i < length del \<Longrightarrow> {Var (x i), t i} \<subseteq> set (eqc i) \<and> Var (x i) \<noteq> t i 
       \<and> (eqc i) \<in> set (del ! i) \<and> snd (x i) = s \<and> t i : s in \<T>(C,\<V>)"
    by blast
  let ?Var = "Var :: nat \<times> 's \<Rightarrow> ('f, nat \<times> 's)term" 
  define n where "n = length del - 1" 
  from del have id: "i < length del \<longleftrightarrow> i \<le> n" for i unfolding n_def by (cases del, auto)
  have "card (t ` {0..n}) \<le> card {0..n}" 
    by (intro card_image_le, auto)
  also have "\<dots> = Suc n" by auto
  also have "Suc n = length del" unfolding n_def using del by (cases del, auto)
  also have "\<dots> < cd_sort s" by fact
  also have "\<dots> = min k (card_of_sort C s)" unfolding cd[OF s(1)] by auto
  also have "\<dots> \<le> card_of_sort C s" by auto 
  finally have "card (t ` {0..n}) < card_of_sort C s" by auto
  {
    fix y
    assume "y \<in> tvars_spat (mset3 (mset3' keep))" 
    hence "y \<in> tvars_spat (set3 keep)" by simp
    with keep have y: "snd y \<noteq> s" by auto
    have "Var y \<notin> (t ` {0..n} \<union> (Var \<circ> x) ` {0..n})" 
    proof
      assume "Var y \<in> (t ` {0..n} \<union> (Var \<circ> x) ` {0..n})" 
      then obtain i where i: "i \<le> n" and ti: "t i = Var y \<or> x i = y" by auto
      from xte[unfolded id, OF i] ti have "snd y = s" by auto
      with y show False by auto
    qed
  } note disjoint = this
  have Sucn: "Suc n = length del" unfolding n_def using del by (cases del, auto)
  have step: "mset3' keep + mset (map (mset2' o (!) del) [0..< Suc n]) \<Rightarrow>\<^sub>s\<^sub>s {# mset3' keep #}" 
    apply (rule spp_delete_large_sort[of n x s "mset o eqc" _  t])
    subgoal for i using xte[unfolded id, of i] by auto
    subgoal using disjoint by force
    subgoal by fact
    done
  from part1 have "mset p = mset del + mset keep" by auto
  hence "mset3' p = mset3' keep + mset3' del" by simp
  also have "del = map ((!) del) [0..< length del]" 
    by (intro nth_equalityI, auto)
  also have "mset3' \<dots> = mset (map (mset2' o (!) del) [0..< Suc n])" unfolding Sucn o_def
    unfolding mset_map image_mset.compositionality o_def ..
  finally have step: "mset3' p \<Rightarrow>\<^sub>s\<^sub>s {# mset3' keep #}" using step by auto 
  show ?thesis
    by (rule exI, intro conjI, rule step, rule ap', insert part1, auto)
qed

lemma simplify_mp: assumes "finite_constructor_form_mp (set2 mp)"  
  and res: "res = simplify_mp (add2 mp)" 
  and vars: "tvars_smp (set2 mp) \<subseteq> V" 
shows "res = Some amp' \<Longrightarrow> 
         \<exists> mp'. amp' = add2 mp' \<and> (\<rightarrow>\<^sub>s\<^sub>s)\<^sup>*\<^sup>* (mset2' mp) (mset2' mp') \<and> simplified_mp amp' \<and> tvars_smp (set2 mp') \<subseteq> V" 
    "res = None \<Longrightarrow> \<exists> mp'. (\<rightarrow>\<^sub>s\<^sub>s)\<^sup>*\<^sup>* (mset2' mp) mp' \<and> smp_fail_ms mp'" 
proof -
  from res[unfolded simplify_mp_def]
  have res: "res = simplify_mp_main (add2 mp) []" (is "_ = simplify_mp_main _ ?Nil") by auto
  have all: "\<forall>eqc\<in>set ?Nil. P eqc" for P by auto
  have "rel_smp mp (add2 mp @ []) (mset2' mp)" 
    unfolding rel_smp_def using assms(1) by blast
  note main = simplify_mp_main[OF this res _ vars refl, OF all, folded simplified_mp_def]
  show "res = None \<Longrightarrow> \<exists> mp'. (\<rightarrow>\<^sub>s\<^sub>s)\<^sup>*\<^sup>* (mset2' mp) mp' \<and> smp_fail_ms mp'" 
    using main(2) by auto
  assume "res = Some amp'" 
  from main(1)[OF this] obtain mp' mpm'
    where rel: "rel_smp mp' amp' mpm'" and steps: "(\<rightarrow>\<^sub>s\<^sub>s)\<^sup>*\<^sup>* (mset2' mp) mpm'" 
      and smp: "simplified_mp amp'" 
      and vars: "tvars_smp (set2 mp') \<subseteq> V"
    by auto
  show "\<exists> mp'. amp' = add2 mp' \<and> (\<rightarrow>\<^sub>s\<^sub>s)\<^sup>*\<^sup>* (mset2' mp) (mset2' mp') \<and> simplified_mp amp' \<and> tvars_smp (set2 mp') \<subseteq> V" 
  proof (intro exI[of _ mp'] conjI steps smp vars)
    from rel_smpD[OF rel] steps
    show "amp' = add2 mp'" "(\<rightarrow>\<^sub>s\<^sub>s)\<^sup>*\<^sup>* (mset (map mset mp)) (mset (map mset mp'))" 
      by auto
  qed
qed

lemma simplify_pp: assumes "finite_constructor_form_pat (set3 p)"
  and "res = simplify_pp (add3 p)"
  and "tvars_spat (set3 p) \<subseteq> V \<and> length p < k" 
shows "res = Some ap' \<Longrightarrow> \<exists> p'. ap' = add3 p'
         \<and> (add_mset (mset3' p) P, add_mset (mset3' p') P) \<in> (\<Rrightarrow>\<^sub>s\<^sub>s)\<^sup>*
         \<and> simplified_pp ap'
         \<and> finite_constructor_form_pat (set3 p')
         \<and> tvars_spat (set3 p') \<subseteq> V \<and> length p' < k"
        (is "?A \<Longrightarrow> ?B")
    and "res = None \<Longrightarrow> (add_mset (mset3' p) P, P) \<in> (\<Rrightarrow>\<^sub>s\<^sub>s)\<^sup>*" (is "?C \<Longrightarrow> ?D")
proof - 
  define p2 :: "('f, nat \<times> 's) term list list list" where "p2 = []" 
  from assms have fin: "finite_constructor_form_pat (set3 (p @ p2))" unfolding p2_def by auto
  from assms have res: "res = map_option ((@) (add3 p2)) (simplify_pp (add3 p))" 
    by (cases "simplify_pp (add3 p)", auto simp: p2_def)
  have smp: "simplified_pp (add3 p2)" unfolding p2_def simplified_pp_def by auto
  have vars: "tvars_spat (set3 (p @ p2)) \<subseteq> V  \<and> length (p @ p2) < k" using assms(3) unfolding p2_def by auto
  have main: "res = Some ap' \<Longrightarrow> \<exists> p'. ap' = add3 p' \<and> 
     (add_mset (mset3' (p @ p2)) P, add_mset (mset3' p') P) \<in> (\<Rrightarrow>\<^sub>s\<^sub>s)\<^sup>* \<and> simplified_pp ap'
       \<and> finite_constructor_form_pat (set3 p') \<and> tvars_spat (set3 p') \<subseteq> V  \<and> length p' < k" 
     "res = None \<Longrightarrow> (add_mset (mset3' (p @ p2)) P, P) \<in> (\<Rrightarrow>\<^sub>s\<^sub>s)\<^sup>*" 
    using fin res smp vars
  proof (atomize(full), induct p arbitrary: ap' p2 res)
    case (Nil res)
    thus ?case by (auto simp: simplified_pp_def)
  next
    case (Cons mp p ap' p2 res)
    have res: "res = map_option ((@) (add3 p2)) (simplify_pp (add3 (mp # p)))" using Cons by auto
    from Cons(2) have fin: "finite_constructor_form_mp (set2 mp)" 
      and finp: "finite_constructor_form_pat (set3 (p @ p2))" 
      and fin_both: "finite_constructor_form_pat (mset3 (add_mset (mset2' mp) (mset3' p + mset3' p2)))" 
      by (auto simp: finite_constructor_form_pat_def image_comp)
    from Cons(5) have tv_mp: "tvars_smp (set2 mp) \<subseteq> V"
        and tv_pp2: "tvars_spat (set3 (p @ p2)) \<subseteq> V \<and> length (p @ p2) < k"
        and k: "Suc (length (p @ p2)) < k" by auto
    show ?case 
    proof (cases "simplify_mp (add2 mp)")
      case None
      with res have res: "res = map_option ((@) (add3 p2)) (simplify_pp (add3 p))" by auto
      from simplify_mp(2)[OF fin refl tv_mp None]
      obtain mp' where steps: "(\<rightarrow>\<^sub>s\<^sub>s)\<^sup>*\<^sup>* (mset2' mp) mp'" and fail: "smp_fail_ms mp'" by auto
      from mp_steps_cong[OF fin_both steps, of P] 
      have steps: "(add_mset (mset3' (mp # p) + mset3' p2) P, add_mset (add_mset mp' (mset3' p + mset3' p2)) P) \<in> (\<Rrightarrow>\<^sub>s\<^sub>s)\<^sup>*" 
        and fin': "finite_constructor_form_pat (mset3 (add_mset mp' (mset3' p + mset3' p2)))" 
        by auto    
      have "(add_mset (add_mset mp' (mset3' p + mset3' p2)) P, {#mset3' p + mset3' p2#} + P) \<in> \<Rrightarrow>\<^sub>s\<^sub>s" 
        by (rule spp_non_det_step, rule spp_delete[OF fail], insert fin', auto)
      with steps have steps: "(add_mset (mset3' (mp # p @ p2)) P, add_mset (mset3' (p @ p2)) P) \<in> (\<Rrightarrow>\<^sub>s\<^sub>s)\<^sup>*" by auto
      note IH = Cons(1)[OF finp res Cons(4) tv_pp2]
      from IH steps res show ?thesis by (cases "simplify_pp (add3 p)"; force)
    next
      case (Some amp')
      from res Some
      have res: "res = map_option ((@) (add3 p2))
          (if amp' = [] then None else map_option ((#) amp') (simplify_pp (add3 p)))" by auto
      from simplify_mp(1)[OF fin refl tv_mp Some] obtain mp' where
        eq: "amp' = add2 mp'" and steps: "(\<rightarrow>\<^sub>s\<^sub>s)\<^sup>*\<^sup>* (mset2' mp) (mset2' mp')" and smp: "simplified_mp amp'" 
        and tvmp': "tvars_smp (set2 mp') \<subseteq> V" 
        by auto
      have fin_cong: "finite_constructor_form_pat (mset3 (add_mset (mset2' mp) (mset3' (p @ p2))))" 
        using fin fin_both by auto
      from mp_steps_cong[OF fin_both steps, of P] 
      have steps: "(add_mset (mset3' (mp # (p @ p2))) P, add_mset (mset3' (mp' # (p @ p2))) P) \<in> (\<Rrightarrow>\<^sub>s\<^sub>s)\<^sup>*" 
        and fin': "finite_constructor_form_pat (mset3 (mset3' (mp' # p @ p2)))" 
        by auto
      show ?thesis
      proof (cases "amp' = []")
        case True
        with res have res: "res = None" by auto
        from True eq have mp': "mp' = []" by auto
        have step: "mset3' (mp' # (p @ p2)) \<Rightarrow>\<^sub>s\<^sub>s {#}" unfolding mp'
          by (simp, rule spp_solved)
        have "(add_mset (mset3' (mp' # (p @ p2))) P, {#} + P) \<in> \<Rrightarrow>\<^sub>s\<^sub>s" 
          by (rule spp_non_det_step[OF step fin'])
        with steps res 
        show ?thesis by auto
      next
        case False
        with res eq have res: "res = map_option ((@) (add3 (p2 @ [mp']))) (simplify_pp (add3 p))" 
          by (cases "simplify_pp (add3 p)", auto)
        from Cons(4) smp eq False eq have "simplified_pp (add3 (p2 @ [mp']))" by (auto simp: simplified_pp_def)
        note IH = Cons(1)[OF _ res this]
        from fin' have fin'': "finite_constructor_form_pat (set3 (p @ p2 @ [mp']))" 
          by (simp add: image_comp image_Un)
        note IH = IH[OF fin''] tvmp' tv_pp2 k
        with IH steps res show ?thesis by (cases "simplify_pp (add3 (p @ p2))"; force)
      qed
    qed
  qed
  from main(1)[unfolded p2_def] show "?A \<Longrightarrow> ?B" by auto
  from main(2)[unfolded p2_def] show "?C \<Longrightarrow> ?D" by auto
qed

lemma inst_list_result: assumes "finite_constructor_form_pat (set3 p)"
  shows "inst_list n x (add3 p)
    = map add3 (map (\<lambda> \<tau>. (map (map (map (\<lambda>t. t \<cdot> \<tau>))) p)) (\<tau>s_list n x))" 
  unfolding map_map o_def s\<tau>s_list_def \<tau>s_list_def inst_list_def
proof (intro map_cong refl, goal_cases)
  case (1 fs mp eqc t)
  from 1 assms have "finite_constructor_form_mp (set2 mp)" by (auto simp: finite_constructor_form_pat_def)
  with 1 obtain s where "t : s in \<T>(C,\<V> |` SS)" by (auto simp: finite_constructor_form_mp_def)
  hence t: "t : s in \<T>(C,\<V>)" by (rule typed_restrict_imp_typed)
  from 1[unfolded Cl] obtain f ss where fs: "fs = (f,ss)" and f: "f : ss \<rightarrow> snd x in C" by auto
  show "add_sort t \<cdot> s\<tau>c n x fs = add_sort (t \<cdot> \<tau>c n x fs)" using add_sort_\<tau>c[OF f t] fs by auto
qed

lemma inst_list: assumes "{#{#Var x, t#}#} \<in># mset3' p" 
  "is_Fun t" 
  "tvars_spat (set3 p) \<subseteq> {..<n} \<times> UNIV \<and> length p < k"
  "finite_constructor_form_pat (set3 p)" 
shows "\<exists> ps'. mset3' p \<Rightarrow>\<^sub>s\<^sub>s mset (map mset3' ps') \<and> map add3 ps' = inst_list n x (add3 p) 
  \<and> Ball (set ps') (\<lambda> p'. tvars_spat (set3 p') \<subseteq> {..<n+m} \<times> UNIV \<and> length p' < k)" 
proof -
  note comp = o_def image_comp mset_map set_mset_mset image_mset.compositionality set_image_mset
  have "fst ` tvars_spat (mset3 (mset3' p)) \<inter> {n..<n + m} = {}" 
    using assms(3) unfolding comp by fastforce
  from spp_inst[OF assms(1-2) this] 
  have step: "mset3' p \<Rightarrow>\<^sub>s\<^sub>s mset (map (\<lambda>\<tau>. image_mset (image_mset (image_mset (\<lambda>t. t \<cdot> \<tau>))) 
               (mset3' p)) (\<tau>s_list n x))" .
  {
    fix t eqc mp \<tau>
    assume t: "t \<in> set eqc" "eqc \<in> set mp" "mp \<in> set p" and tau: "\<tau> \<in> set (\<tau>s_list n x)" 
    from t assms(3) have "fst ` vars t \<subseteq> {..<n}" by fastforce
    with tau m have "fst ` vars (t \<cdot> \<tau>) \<subseteq> {..<n} \<union> {..<n+m}" unfolding \<tau>s_list \<tau>s_def \<tau>c_def
      by (auto simp: subst_def vars_term_subst split: if_splits simp: set_zip) (fastforce+)
    hence "fst ` vars (t \<cdot> \<tau>) \<subseteq> {..< n + m}" by auto
  } note vars = this    
  show ?thesis 
    apply (intro exI, rule conjI[OF _ conjI[OF inst_list_result[OF assms(4), symmetric]]])
     apply (unfold comp, rule step[unfolded comp])
    apply (intro ballI conjI)
     apply clarsimp subgoal for tau x s mp eqc t using vars[of t eqc mp tau] by auto
    using assms by auto
qed

lemma simplified_mp_add2: "simplified_mp (add2 mp) = simplified_mp mp"
  unfolding simplified_mp_def
  by (auto simp: distinct_map inj_on_def)

lemma simplified_pp_add3: "simplified_pp (add3 p) = simplified_pp p" 
  unfolding simplified_pp_def by (simp add: simplified_mp_add2)

fun simpl_tag :: "('f,'s)tagged_simple_pat_problem_slist \<Rightarrow> bool" where
  "simpl_tag (False,p) = True"  
| "simpl_tag (True,p) = simplified_pp p" 

lemma simplify_tpp: assumes inv: "simpl_tag (tag, add3 p)"
  and res: "res = simplify_tpp (tag, add3 p)"
  and fin: "finite_constructor_form_pat (set3 p)" 
  and vars: "tvars_spat (set3 p) \<subseteq> V \<and> length p < k" 
shows "res = Some (tag',ap') \<Longrightarrow> \<exists> p'. ap' = add3 p'
         \<and> (add_mset (mset3' p) P, add_mset (mset3' p') P) \<in> (\<Rrightarrow>\<^sub>s\<^sub>s)\<^sup>*
         \<and> tag' = True
         \<and> simpl_tag (tag',ap')  
         \<and> finite_constructor_form_pat (set3 p')       
         \<and> tvars_spat (set3 p') \<subseteq> V  \<and> length p' < k"        
    and "res = None \<Longrightarrow> (add_mset (mset3' p) P, P) \<in> (\<Rrightarrow>\<^sub>s\<^sub>s)\<^sup>*" 
proof (atomize(full), goal_cases)
  case 1
  show ?case
  proof (cases tag)
    case True
    thus ?thesis using assms by auto
  next
    case False
    show ?thesis
    proof (cases "simplify_pp (add3 p)")
      case None
      from simplify_pp(2)[OF fin refl vars None, of P] None res
      show ?thesis using False by auto
    next
      case (Some ap')
      from simplify_pp(1)[OF fin refl vars Some, of P] Some res
      show ?thesis using False by (auto simp: simplified_pp_add3)
    qed
  qed
qed


abbreviation add4 where "add4 \<equiv> map (map_prod id add3)" 
abbreviation mset4' where "mset4' \<equiv> image_mset (mset3' o snd) o mset" 

lemma full_step: assumes tvarsp: "tvars_spat (set3 p) \<subseteq> {..<n} \<times> UNIV \<and> length p < k"
  and finp: "finite_constructor_form_pat (set3 p)" 
  and inv_tag: "simpl_tag (tag,add3 p)" 
  and result: "full_step n (tag,add3 p) = res"
shows "res = Inl aps \<Longrightarrow> \<exists> ps. aps = add4 ps 
            \<and> (add_mset (mset3' p) P, mset4' ps + P) \<in> (\<Rrightarrow>\<^sub>s\<^sub>s)\<^sup>+
            \<and> Ball (snd ` set ps) (\<lambda> p'. tvars_spat (set3 p') \<subseteq> {..< n + m} \<times> UNIV \<and> length p' < k)
            \<and> Ball (set aps) simpl_tag"
  "res = Inr fvf \<Longrightarrow> simplified_pp (map (map (map (Var :: _ \<Rightarrow> ('f,_)term))) fvf) \<and> length fvf < k
      \<and> (add_mset (mset3' p) P, add_mset (mset3' (map (map (map Var)) fvf)) P) \<in> (\<Rrightarrow>\<^sub>s\<^sub>s)\<^sup>*
      \<and> (\<forall> x \<iota>. (x,\<iota>) \<in> set (concat (concat fvf)) \<longrightarrow> card_of_sort C \<iota> < k)"
proof (atomize(full), goal_cases)
  case 1
  note res = result[symmetric, unfolded full_step_def]
  show ?case
  proof (cases "simplify_tpp (tag,add3 p)")
    case None
    with res have res: "res = Inl []" by auto
    from simplify_tpp(2)[OF inv_tag refl finp tvarsp None, of P]
    have "(add_mset (mset3' p) P, P) \<in> (\<Rrightarrow>\<^sub>s\<^sub>s)\<^sup>*" .
    hence "(add_mset (mset3' p) P, P) \<in> (\<Rrightarrow>\<^sub>s\<^sub>s)\<^sup>+"
      by (simp add: rtrancl_eq_or_trancl)
    with res show ?thesis by auto
  next
    case (Some tap1)
    then obtain tag' ap1 where Some: "simplify_tpp (tag, add3 p) = Some (tag', ap1)" by (cases tap1, auto)
    from simplify_tpp(1)[OF inv_tag refl finp tvarsp Some, of P]
    obtain p' where ap1: "ap1 = add3 p'" 
      and steps': "(add_mset (mset3' p) P, add_mset (mset3' p') P) \<in> (\<Rrightarrow>\<^sub>s\<^sub>s)\<^sup>*" 
      and finp': "finite_constructor_form_pat (set3 p')" 
      and simpl': "simplified_pp (add3 p')"
      and tag': "tag' = True" 
      and tvarsp': "tvars_spat (set3 p') \<subseteq> {..<n} \<times> UNIV \<and> length p' < k" 
      by auto
    note res = res[unfolded Some option.simps ap1 tag' split bool.simps]
    show ?thesis
    proof (cases "large_sort_impl (add3 p')")
      case (Some ap2)
      have res: "res = Inl [(True, ap2)]" using res[unfolded Some] by simp
      from large_sort_impl[OF Some finp' simpl'[unfolded simplified_pp_add3]]
      obtain p2 where step: "mset3' p' \<Rightarrow>\<^sub>s\<^sub>s {#mset3' p2#}" and ap2:  "ap2 = add3 p2" 
        and sub: "set p2 \<subseteq> set p'" "length p2 \<le> length p'" by auto
      from sub simpl' 
      have simpl2: "simplified_pp (add3 p2)" 
        unfolding simplified_pp_add3 unfolding simplified_pp_def by auto
      have vars: "tvars_spat (set3 p2) \<subseteq> {..<n+m} \<times> UNIV  \<and> length p2 < k" 
        using sub tvarsp' by fastforce
      from steps' spp_non_det_step[OF step, unfolded mset3_mset3'_set3, OF finp']
      have steps: "(add_mset (mset3' p) P, {#mset3' p2#} + P) \<in> (\<Rrightarrow>\<^sub>s\<^sub>s)\<^sup>+" 
        by (rule rtrancl_into_trancl1)
      show ?thesis unfolding res ap2 using steps vars simpl2
        by (intro conjI impI exI[of _ "[(True,p2)]"], auto)
    next
      case clNone: None
      note res = res[unfolded clNone option.simps]
      show ?thesis
      proof (cases "search_fun_pp (add3 p')")
        case None
        from res[unfolded None] have res: "res = Inr (map (map (map the_Var)) (add3 p'))" (is "_ = Inr ?fvf") by auto
        have id: "map (map (map Var)) ?fvf = p'" unfolding map_map o_def
        proof (intro map_idI, goal_cases)
          case (1 mp eqc t)
          with search_fun_pp_None[OF None] have "is_Var t" by force
          thus "Var (the_Var (add_sort t)) = t" by (cases t, auto)
        qed
        {
          fix mp eqc  x \<iota> t
          assume *: "mp \<in> set p'" "eqc \<in> set mp" "t \<in> set eqc" "(x, \<iota>) = the_Var (add_sort t)" 
          with search_fun_pp_None[OF None] have "is_Var t" by force
          with * have t: "t = Var (x,\<iota>)" by (cases t, auto)
          define terms where "terms = concat (concat (add3 p'))" 
          have tterms: "add_sort t \<in> set terms" unfolding terms_def using * by auto
          define sorts where "sorts = remdups (map sort_of terms)" 
          from t tterms have \<iota>sorts: "\<iota> \<in> set sorts" unfolding sorts_def by force
          from clNone[unfolded large_sort_impl_def Let_def, folded terms_def, folded sorts_def]
          have "extract_option (large_sort_impl_main (add3 p')) sorts = None" by auto
          (* the sort \<iota> cannot be removed by large-sort *)
          from this[unfolded extract_option_None] \<iota>sorts
          have largeNone: "large_sort_impl_main (add3 p') \<iota> = None" by auto
          (* therefore it must have a small cardinality *)
          define find_confl where "find_confl = (\<lambda>mp. \<exists>eqc\<in>set mp. sort_of (hd (eqc :: ('f \<times> 's, nat \<times> 's) Term.term list)) = \<iota>)" 
          obtain del keep where part: "partition find_confl (add3 p') = (del,keep)" by force
          from largeNone[unfolded large_sort_impl_main_def, folded find_confl_def, unfolded part Let_def split]
          have fail: "del = [] \<or> length del \<ge> cd_sort \<iota> \<or> (\<exists>mp\<in>set keep. \<exists>eq\<in>set mp. \<exists>t\<in>set eq. \<exists>x\<in>set (vars_term_list t). snd x = \<iota>)" 
            by (auto split: if_splits)
          from finp' have finmp: "finite_constructor_form_mp (set2 mp)" using * 
            unfolding finite_constructor_form_pat_def by auto
          from * have "set eqc \<in> set2 mp" by auto
          from finmp[unfolded finite_constructor_form_mp_def, rule_format, OF this]
          obtain \<iota>' where same: "\<And> t. t \<in> set eqc \<Longrightarrow> t : \<iota>' in \<T>(C,\<V> |` SS)" by auto
          from this[OF *(3), unfolded t] have "\<iota>' = \<iota>" and inS: "\<iota> \<in> S" by (auto simp add: hastype_def restrict_map_def split: if_splits)
          note same = same[unfolded this]
          have "find_confl (add2 mp)" unfolding find_confl_def
          proof (intro bexI[of _ "add1 eqc"])
            show "add1 eqc \<in> set (add2 mp)" using * by auto
            from * obtain t ts where eqc: "eqc = t # ts" by (cases eqc, auto)
            from same[of t, unfolded this] have "t : \<iota> in \<T>(C,\<V> |` SS)" by auto
            hence "t : \<iota> in \<T>(C,\<V>)" by (rule typed_restrict_imp_typed)
            with eqc show "sort_of (hd (add1 eqc)) = \<iota>" using add_sort[of t \<iota>] by simp
          qed
          with * part have "add2 mp \<in> set del" by auto
          hence "del \<noteq> []" by auto
          with fail have fail: "length del \<ge> cd_sort \<iota> \<or> (\<exists>mp\<in>set keep. \<exists>eq\<in>set mp. \<exists>t\<in>set eq. \<exists>x\<in>set (vars_term_list t). snd x = \<iota>)" 
            (is "_ \<or> ?exists")
            by auto
          hence "card_of_sort C \<iota> < k"
          proof
            assume len: "length del \<ge> cd_sort \<iota>" 
            from part have "length del \<le> length p'" by auto
            with tvarsp' have "length del < k" by auto
            with len have "k > cd_sort \<iota>" by auto
            from this[unfolded cd[OF inS]]
            show ?thesis by simp
          next
            assume ?exists
            then obtain mp' eq' t' x where **: "mp' \<in> set keep" "eq' \<in> set mp'" "t' \<in> set eq'" "x \<in> vars t'" "snd x = \<iota>" 
              by auto
            from **(1) part have mp': "mp' \<in> set (add3 p')" and "\<not> find_confl mp'" by auto
            from this(2)[unfolded find_confl_def] ** 
            have neq: "sort_of (hd eq') \<noteq> \<iota>" by auto
            from mp' obtain mp where mp: "mp \<in> set p'" and mp': "mp' = add2 mp" by auto
            from finp' have finmp: "finite_constructor_form_mp (set2 mp)" using mp
              unfolding finite_constructor_form_pat_def by auto
            from **(2)[unfolded mp'] obtain eq where eq: "eq \<in> set mp" and "set eq \<in> set2 mp" and eq': "eq' = add1 eq" by auto
            from finmp[unfolded finite_constructor_form_mp_def, rule_format, OF this(2)]
            obtain \<iota>' where sort: "t \<in> set eq \<Longrightarrow> t : \<iota>' in \<T>(C,\<V> |` SS)" for t by auto
            from **(3)[unfolded eq'] obtain t where t: "t \<in> set eq" and t': "t' = add_sort t" by auto
            from t eq mp search_fun_pp_None[OF None] have "is_Var t" by force
            with **(4,5) t' obtain y where ty: "t = Var (y,\<iota>)" by (cases t; force)
            from sort[OF t, unfolded ty] have "\<iota>' = \<iota>" by (auto simp add: hastype_def restrict_map_def split: if_splits)
            note sort = sort[unfolded this]
            from t obtain t ts where eq: "eq = t # ts" by (cases eq, auto)
            hence "hd eq' = add_sort t" unfolding eq' by auto
            with neq have neq: "sort_of (add_sort t) \<noteq> \<iota>" by auto
            from sort[of t, unfolded eq] have "t : \<iota> in \<T>(C,\<V> |` SS)" by auto
            hence "t : \<iota> in \<T>(C,\<V>)" by (rule typed_restrict_imp_typed)
            from add_sort[OF this] neq have False by auto
            thus ?thesis ..
          qed
        }
        thus ?thesis unfolding res 
          using steps' id simpl' tvarsp' by (fastforce simp: simplified_pp_add3)
      next
        case (Some result)
        obtain ap1 amp amp1 aeqc aeqc1 at aeqc2 amp2 ap2 where result: "result = (ap1,amp,(amp1,aeqc,(aeqc1,at,aeqc2),amp2),ap2)" 
          by (cases result, auto)
        note res = res[unfolded Some result option.simps split]
        note search = search_fun_pp_Some[OF Some[unfolded result]]
        note ids = search(1-3)
        from ids(1)[unfolded map_eq_append_conv] obtain p1 mp p2 where 
          idp: "ap1 = add3 p1" "amp = add2 mp" "ap2 = add3 p2" "p' = p1 @ mp # p2" 
          by blast
        from ids(2)[unfolded map_eq_append_conv idp] obtain mp1 eqc mp2 where 
          idm: "amp1 = add2 mp1" "aeqc = map add_sort eqc" "amp2 = add2 mp2" "mp = mp1 @ eqc # mp2"
          by blast
        from ids(3)[unfolded map_eq_append_conv idm] obtain eqc1 t eqc2 where 
          ide: "aeqc1 = map add_sort eqc1" "at = add_sort t" "aeqc2 = map add_sort eqc2" "eqc = eqc1 @ t # eqc2"
          by blast

        from search have at: "is_Fun at" "at \<in> set aeqc" by auto
        from simpl'[unfolded simplified_pp_def] ids
        have "simplified_mp amp" by auto
        from this[unfolded simplified_mp_def] ids
        have "Bex (set aeqc) is_Var" by auto
        hence "find is_Var aeqc \<noteq> None" unfolding find_None_iff by auto
        then obtain ax where find: "find is_Var aeqc = Some ax" by auto
        from this[unfolded find_Some_iff]
        have ax: "ax \<in> set aeqc" "is_Var ax" by auto
        from this[unfolded idm] obtain x where x: "x \<in> set eqc" and "is_Var x" and ax: "ax = add_sort x"
          by auto
        then obtain X where X: "x = Var X" by (cases x, auto)
        from find have find: "the (find is_Var aeqc) = ax" by auto
        define long where "long = (aeqc1 @ aeqc2) # amp1 @ amp2"
        define ampn where "ampn = (if length_gt_1 (aeqc1 @ aeqc2) then long else amp1 @ amp2)" 
        note res = res[unfolded find Let_def, folded long_def, folded ampn_def]
        from at ide have t: "is_Fun t" by auto
        let ?cond = "amp = [[at, ax]] \<or> amp = [[ax, at]]" 
        show ?thesis
        proof (cases "?cond")
          case True
          hence "?cond = True" by auto
          with res ax X have res: "res = Inl (map (Pair False) (inst_list n X (add3 p')))" by auto
          from True have "mp = [[t,x]] \<or> mp = [[x,t]]" unfolding idp ax ide by auto
          hence "{#{#Var X, t#}#} \<in># mset3' p'" unfolding idp X by auto
          from inst_list[OF this t tvarsp' finp'] 
          obtain ps' where step: "mset3' p' \<Rightarrow>\<^sub>s\<^sub>s mset (map mset3' ps')" 
            and inst: "map add3 ps' = inst_list n X (add3 p')" 
            and vars: "Ball (set ps') (\<lambda> p'. tvars_spat (set3 p') \<subseteq> {..<n+m} \<times> UNIV \<and> length p' < k)" by blast
          from steps' spp_non_det_step[OF step, unfolded mset3_mset3'_set3, OF finp']
          have steps: "(add_mset (mset3' p) P, mset (map mset3' ps') + P) \<in> (\<Rrightarrow>\<^sub>s\<^sub>s)\<^sup>+" 
            by (rule rtrancl_into_trancl1)
          show ?thesis unfolding res using steps vars inst[symmetric]
            by (intro conjI impI exI[of _ "map (Pair False) ps'"], auto simp: o_def image_mset.compositionality)
        next
          case False
          let ?anew = "((aeqc1 @ aeqc2) # amp1 @ amp2) # ap1 @ ap2" 
          from False res 
          have res: "res = Inl ((True, ampn # ap1 @ ap2) #
            map (Pair False) (inst_list n (the_Var ax) ([[ax, at]] # ap1 @ ap2)))" 
            by auto
          from ide x t X have "x \<in> set (eqc1 @ eqc2)" by auto
          from split_list[OF this] obtain eqc3 eqc4 where eqc12: "eqc1 @ eqc2 = eqc3 @ x # eqc4" by auto
          from arg_cong[OF this, of mset] ide 
          have eqc_xt: "mset eqc = {#x,t#} + mset (eqc3 @ eqc4)" and 
            x34: "add_mset x (mset (eqc3 @ eqc4)) = mset (eqc1 @ eqc2)" by auto
          have diff1: "is_Var x \<noteq> is_Var t" using X t by auto
          from False[unfolded idp ax ide] have "mp \<noteq> [[x,t]] \<and> mp \<noteq> [[t,x]]" by auto
          hence diff2: "mset2' mp \<noteq> {#{#x,t#}#}" 
            apply (cases mp)
             apply force
            subgoal for eqc mp'
              apply (cases mp')
               apply (cases eqc)
                apply force
              subgoal for t1 eqc1
                apply (cases eqc1)
                 apply force
                subgoal for t2 eqc2
                  by (cases eqc2) (auto simp: add_eq_conv_ex)
                done
              apply force
              done
            done
          define np1 where "np1 = [[x,t]] # (p1 @ p2)" 
          define np2 where "np2 = ((eqc1 @ eqc2) # (mp1 @ mp2)) # (p1 @ p2)" 
          define np3 where "np3 = ((mp1 @ mp2)) # (p1 @ p2)" 
          have eq: "mset2' mp = (add_mset (add_mset x (add_mset t (mset (eqc3 @ eqc4)))) (mset2' (mp1 @ mp2)))" 
            unfolding idm by (simp add: eqc_xt)
          with diff2 have "mset (eqc3 @ eqc4) \<noteq> {#} \<or> mset2' (mp1 @ mp2) \<noteq> {#}" by auto
          from spp_split[OF eq diff1 this, unfolded x34, of "mset3' (p1 @ p2)"]
          have step: "mset3' p' \<Rightarrow>\<^sub>s\<^sub>s {# mset3' np1, mset3' np2#}"
            by (simp add: idp idm ide np1_def np2_def )  
          from steps' spp_non_det_step[OF this, unfolded mset3_mset3'_set3, OF finp', of P]
          have steps: "(add_mset (mset (map (\<lambda>mpl. mset (map mset mpl)) p)) P, {# mset3' np1, mset3' np2#} + P) \<in> (\<Rrightarrow>\<^sub>s\<^sub>s)\<^sup>+" 
            by (rule rtrancl_into_trancl1)

          from tvarsp' have tvars1: "tvars_spat (set3 np1) \<subseteq> {..<n} \<times> UNIV \<and> length np1 < k" 
            using x unfolding np1_def idp idm ide 
            by auto
          from tvarsp' have "tvars_spat (set3 np2) \<subseteq> {..<n} \<times> UNIV \<and> length np2 < k" 
            unfolding np2_def idp idm ide by auto
          hence tvars2: "tvars_spat (set3 np2) \<subseteq> {..<n + m} \<times> UNIV \<and> length np2 < k" by fastforce
          from spp_step_ms[OF step, unfolded mset3_mset3'_set3, OF finp']
          have fin1: "finite_constructor_form_pat (set3 np1)" 
            and fin2: "finite_constructor_form_pat (set3 np2)" 
            using mset3_mset3'_set3[of np1] mset3_mset3'_set3[of np2] by auto

          have "{#{#Var X, t#}#} \<in># mset3' np1" unfolding np1_def X by auto
          from inst_list[OF this t tvars1 fin1]
          obtain ps' where step: "mset3' np1 \<Rightarrow>\<^sub>s\<^sub>s mset (map mset3' ps')" 
            and inst: "map add3 ps' = inst_list n X (add3 np1)" 
            and vars: "Ball (set ps') (\<lambda> p'. tvars_spat (set3 p') \<subseteq> {..<n+m} \<times> UNIV \<and> length p' < k)" by blast
          from steps spp_non_det_step[OF step, unfolded mset3_mset3'_set3, OF fin1, of "add_mset (mset3' np2) P"]
          have steps: "(add_mset (mset3' p) P, mset (map mset3' ps') + add_mset (mset3' np2) P) \<in> (\<Rrightarrow>\<^sub>s\<^sub>s)\<^sup>+" 
            by simp
          show ?thesis
          proof (cases "length (aeqc1 @ aeqc2) > 1")
            case True
            hence ampn: "ampn = (aeqc1 @ aeqc2) # amp1 @ amp2" unfolding ampn_def long_def by auto
            note res = res[unfolded this]
            have simpl_tag': "simpl_tag (True, ampn # ap1 @ ap2)"
              using simpl'[unfolded ids] at(1) True unfolding ampn_def long_def 
              by (auto simp: simplified_pp_def simplified_mp_def)
            show ?thesis unfolding res
              apply (intro conjI impI exI[of _ "(True,np2) # map (Pair False) ps'"])
              subgoal using inst[symmetric] by (auto simp: np2_def idp idm ide np1_def X ax o_def)
              subgoal using steps by (auto simp: o_def image_mset.compositionality)
              subgoal using vars tvars2 by auto
              subgoal using simpl_tag' ampn by auto
              by auto
          next
            case len: False
            hence ampn: "ampn = amp1 @ amp2" unfolding ampn_def by auto
            from len eqc12 have eqc12: "eqc1 @ eqc2 = [x]" unfolding ide by (cases eqc1; cases eqc2; auto)  
            from arg_cong[OF this, of mset] have single: "mset eqc1 + mset eqc2 = {# x #}" by simp
            from eqc12 ide have "eqc = [t,x] \<or> eqc = [x,t]" by (cases eqc1; auto)
            hence "aeqc = [at,ax] \<or> aeqc = [ax,at]" using ide ax idm by fastforce
            with False idm idp have ne: "mp1 \<noteq> [] \<or> mp2 \<noteq> []" by (cases mp1, auto)
            have "(add_mset (mset3' np2) (mset (map mset3' ps') +  P), 
             {#mset3' np3#} + (mset (map mset3' ps') +  P)) \<in> \<Rrightarrow>\<^sub>s\<^sub>s" 
              apply (rule spp_non_det_step)
              subgoal 
                apply (simp add: np2_def np3_def single)
                apply (rule spp_simp)
                by (rule smp_singleton)
              subgoal using fin2 mset3_mset3'_set3[of np2] by auto
              done
            with steps 
            have steps: "(add_mset (mset3' p) P, mset (map mset3' ps') + add_mset (mset3' np3) P) \<in> (\<Rrightarrow>\<^sub>s\<^sub>s)\<^sup>+" 
              by simp          
            have simpl_tag': "simpl_tag (True, ampn # ap1 @ ap2)" 
              using simpl'[unfolded ids] ampn ne idm
              by (simp add: simplified_pp_def simplified_mp_def)
            show ?thesis unfolding res ampn
              apply (intro conjI impI exI[of _ "(True,np3) # map (Pair False) ps'"])
              subgoal using inst[symmetric] by (auto simp: np3_def idp idm ide np1_def X ax o_def)
              subgoal using steps by (auto simp: o_def image_mset.compositionality)
              subgoal using vars tvars2 np2_def np3_def by auto
              subgoal using simpl_tag' by (auto simp: ampn)
              by auto
          qed
        qed
      qed
    qed
  qed
qed

context
  fixes solver :: "((nat\<times>'s) \<times> int)list \<times> _ \<Rightarrow> bool" 
  assumes fidl: "finite_idl_solver solver"
begin

lemma pat_complete_via_idl_solver:
  assumes fvf: "finite_var_form_pat C (pat_list pp)"
    and wf: "wf_pat (pat_list pp)"
    and pp: "pp = pat_of_var_form_list fvf" 
    and dist: "Ball (set fvf) (distinct o map fst)" 
    and dist2: "Ball (set (concat fvf)) (distinct o snd)" 
    and small: "(\<forall> x \<iota>. (x,\<iota>) \<in> set (concat (concat cnf)) \<longrightarrow> card_of_sort C \<iota> < k)" 
    and cnf: "cnf = map (map snd) fvf"
  shows "pat_complete C (pat_list pp) \<longleftrightarrow> \<not> solver (bounds_list (cd_sort \<circ> snd) cnf, dist_pairs_list cnf)"
proof-
  let ?S = S
  note vf = finite_var_form_imp_of_var_form_pat[OF fvf]
  have var_conv: "set (concat (concat cnf)) = tvars_pat (pat_list pp)"
    unfolding cnf pp 
    by (force simp: tvars_pat_def pat_list_def tvars_match_def pat_of_var_form_list_def match_of_var_form_list_def)
  {
    fix v
    assume v: "v \<in> tvars_pat (pat_list pp)" 
    with wf[unfolded wf_pat_iff] cd
    have "cd_sort (snd v) = min k (card_of_sort C (snd v))" by auto
    also have "\<dots> = card_of_sort C (snd v)" using v[folded var_conv] small[rule_format, of "fst v" "snd v"]
      by auto
    finally have "cd_sort (snd v) = card_of_sort C (snd v)" .
  } note cd_conv = this
  
  define cd :: "nat \<times> 's \<Rightarrow> nat" where "cd = (cd_sort \<circ> snd)" 
  define S where "S = set (concat (concat cnf))" 
  {
    fix v vs c
    assume "c \<in> set cnf" "vs \<in> set c" "v \<in> set vs" 
    hence "v \<in> S" unfolding S_def by auto
  } note in_S = this
  have "pat_complete C (pat_list pp) \<longleftrightarrow>
    (\<forall>\<alpha>. (\<forall>v\<in> S. \<alpha> v < cd v) \<longrightarrow> (\<exists>c\<in>set cnf. \<forall>vs\<in>set c. UNIQ (\<alpha> ` set vs)))" 
    by (unfold S_def pat_complete_via_cnf[OF fvf pp dist cnf] var_conv, simp add: cd_conv cd_def)
  also have "\<dots> \<longleftrightarrow> \<not> (\<exists> \<alpha>. (\<forall>v\<in> S. \<alpha> v < cd v) \<and> (\<forall> c \<in> set cnf. \<exists>vs\<in>set c. \<not> UNIQ (\<alpha> ` set vs)))" (is "_ \<longleftrightarrow> \<not> ?f") by blast
  also have "?f \<longleftrightarrow> (\<exists> \<alpha>. (\<forall>v\<in> S. \<alpha> v < cd v) \<and> (\<forall>c\<in>set cnf. \<exists>vs\<in>set c. \<exists>v\<in>set vs. \<exists>w\<in>set vs. \<alpha> v \<noteq> \<alpha> w))" (is "_ \<longleftrightarrow> (\<exists> \<alpha>. ?fN \<alpha>)")
    unfolding non_uniq_image_diff ..
  also have "\<dots> \<longleftrightarrow> (\<exists> \<alpha>. (\<forall>v\<in> S. 0 \<le> \<alpha> v \<and> \<alpha> v < int (cd v)) \<and> (\<forall>c\<in>set cnf. \<exists>vs\<in>set c. \<exists>v\<in>set vs. \<exists>w\<in>set vs. \<alpha> v \<noteq> \<alpha> w))" (is "_ \<longleftrightarrow> (\<exists> \<alpha>. ?fZ \<alpha>)")
  proof
    assume "\<exists> \<alpha>. ?fN \<alpha>" 
    then obtain \<alpha> where "?fN \<alpha>" by blast
    hence "?fZ (int o \<alpha>)" unfolding o_def by auto
    thus "\<exists> \<alpha>. ?fZ \<alpha>" by blast
  next
    assume "\<exists> \<alpha>. ?fZ \<alpha>" 
    then obtain \<alpha> where alpha: "?fZ \<alpha>" by blast
    have "?fN (nat o \<alpha>)" unfolding o_def
    proof (intro conjI ballI)
      show "v \<in> S \<Longrightarrow> nat (\<alpha> v) < cd v" for v using alpha by auto
      fix c
      assume c: "c \<in> set cnf" 
      with alpha obtain vs v w where vs: "vs\<in>set c" and v: "v\<in>set vs" and w: "w\<in>set vs" and diff: "\<alpha> v \<noteq> \<alpha> w" 
        by auto
      from in_S[OF c vs] v w have "v \<in> S" "w \<in> S" by auto
      with alpha have "\<alpha> v \<ge> 0" "\<alpha> w \<ge> 0" by auto 
      with diff have "nat (\<alpha> v) \<noteq> nat (\<alpha> w)" by simp
      with vs v w show "\<exists>vs\<in>set c. \<exists>v\<in>set vs. \<exists>w\<in>set vs. nat (\<alpha> v) \<noteq> nat (\<alpha> w)" by auto
    qed
    thus "\<exists> \<alpha>. ?fN \<alpha>" by blast
  qed
  also have "\<dots> \<longleftrightarrow> (\<exists> \<alpha>. (\<forall>v\<in> S. 0 \<le> \<alpha> v \<and> \<alpha> v \<le> int (cd v) - 1) \<and> (\<forall>c\<in>set cnf. \<exists>vs\<in>set c. \<exists>v\<in>set vs. \<exists>w\<in>set vs. \<alpha> v \<noteq> \<alpha> w))" 
    by auto
  also have "\<dots> = (\<exists>\<alpha>. (\<forall>(v, b)\<in>set (bounds_list cd cnf). 0 \<le> \<alpha> v \<and> \<alpha> v \<le> b) \<and> (\<forall>c\<in>set (dist_pairs_list cnf). \<exists>(v, w)\<in>set c. \<alpha> v \<noteq> \<alpha> w))" 
    unfolding bounds_list_def Let_def S_def[symmetric] set_map set_remdups
  proof (intro arg_cong[of _ _ "Ex"] ext arg_cong2[of _ _ _ _ "(\<and>)"], force)
    fix \<alpha> :: "_ \<Rightarrow> int" 
    show "(\<forall>c\<in>set cnf. \<exists>vs\<in>set c. \<exists>v\<in>set vs. \<exists>w\<in>set vs. \<alpha> v \<noteq> \<alpha> w) = (\<forall>c\<in>set (dist_pairs_list cnf). \<exists>(v, w)\<in>set c. \<alpha> v \<noteq> \<alpha> w)"
      unfolding diff_pairs_of_list dist_pairs_list_def set_map image_comp set_concat o_def
      by force
  qed
  also have "\<dots> = fidl_solvable (bounds_list cd cnf, dist_pairs_list cnf)" 
    unfolding fidl_solvable_def split ..
  also have "\<dots> = solver (bounds_list cd cnf,dist_pairs_list cnf)" 
  proof (rule sym, rule fidl[unfolded finite_idl_solver_def, rule_format])
    show "fidl_input (bounds_list cd cnf, dist_pairs_list cnf)" unfolding fidl_input_def split
    proof (intro conjI allI impI)
      show "(x, y) \<in> set (concat (dist_pairs_list cnf)) \<Longrightarrow> z \<in> {x, y} \<Longrightarrow> z \<in> fst ` set (bounds_list cd cnf)" for x y z
        unfolding dist_pairs_list_def bounds_list_def List.maps_eq set_concat set_map image_comp o_def
          set_pairs_of_list by force
      show "distinct (map fst (bounds_list cd cnf))" unfolding bounds_list_def Let_def map_map o_def 
        by auto
      show "\<And>v w b1 b2.
       (v, b1) \<in> set (bounds_list cd cnf) \<Longrightarrow>
       (w, b2) \<in> set (bounds_list cd cnf) \<Longrightarrow> snd v = snd w \<Longrightarrow> b1 = b2" 
        unfolding bounds_list_def Let_def by (auto simp: cd_def)
      {
        fix v b
        assume "(v, b) \<in> set (bounds_list cd cnf)"
        from this[unfolded bounds_list_def] 
        have v: "v \<in> tvars_pat (pat_list pp)" and b: "b = int (cd v) - 1" by (auto simp flip: var_conv)
        from cd_conv[OF v] b have b: "b = int (card_of_sort C (snd v)) - 1" by (auto simp: cd_def)
        from wf[unfolded wf_pat_iff, rule_format, OF v] 
        have vS: "snd v \<in> ?S" by auto
        from not_empty_sort[OF this] 
        have nE: "\<not> empty_sort C (snd v)" .
        from v[unfolded tvars_pat_def tvars_match_def]
        obtain mp t l where mp: "mp \<in> pat_list pp" and tl: "(t,l) \<in> mp" and vt: "v \<in> vars t" by auto
        from fvf[unfolded finite_var_form_pat_def] mp have mp: "finite_var_form_match C mp" by auto
        note mp = mp[unfolded finite_var_form_match_def]
        from mp[unfolded var_form_match_def] tl obtain x where t: "t = Var x" by auto
        with vt tl have vl: "(Var v, l) \<in> mp" by auto
        with mp have "finite_sort C (snd v)" by blast
        with nE have "card_of_sort C (snd v) > 0" unfolding empty_sort_def finite_sort_def card_of_sort_def 
          by fastforce
        thus "0 \<le> b" unfolding b by simp
      }
      fix v w
      assume "(v, w) \<in> set (concat (dist_pairs_list cnf))" 
      from this[unfolded dist_pairs_list_def cnf, simplified]
      obtain c x vs where c: "c \<in> set fvf" and xvs: "(x,vs) \<in> set c" and vw: "(v, w) \<in> set (pairs_of_list vs)" 
        by auto
      from dist2 c xvs have dist2: "distinct vs" by force
      from vw[unfolded set_pairs_of_list] 
      obtain i where v: "v = vs ! i" and w: "w =  vs ! Suc i" and i: "Suc i < length vs" by auto
      from dist2 v w i show "v \<noteq> w" unfolding distinct_conv_nth by simp

      from v w i have vw: "v \<in> set vs" "w \<in> set vs" by auto
      from fvf[unfolded pp finite_var_form_pat_def pat_list_def pat_of_var_form_list_def] c
      have "finite_var_form_match C (set (match_of_var_form_list c))" by auto
      from this[unfolded finite_var_form_match_def, THEN conjunct2, THEN conjunct1, rule_format, of v "Var x" w]
      show "snd v = snd w" using vw xvs unfolding match_of_var_form_list_def by auto
    qed
  qed
  finally show ?thesis unfolding cd_def .
qed 

lemma fvf_solver: assumes tfvf: "tfvf = map (map (map (Var :: nat \<times> 's \<Rightarrow> ('f, nat \<times> 's)term))) fvf" 
  and small: "(\<forall> x \<iota>. (x,\<iota>) \<in> set (concat (concat fvf)) \<longrightarrow> card_of_sort C \<iota> < k)" 
  and fin: "finite_constructor_form_pat (set3 tfvf)" 
  and simpl: "simplified_pp tfvf" 
shows "fvf_solver solver fvf = simple_pat_complete C SS (set3 tfvf)" 
proof -
  {
    fix eqc :: "(nat \<times> 's) list" 
    have "set (zip eqc (tl eqc)) = (\<lambda> i. (eqc ! i, eqc ! (Suc i))) ` {..< length eqc - 1}" 
      unfolding set_zip by (cases eqc, auto)
  } note set_zip_eqc = this
  let ?Var = "Var :: nat \<times> 's \<Rightarrow> ('f, nat \<times> 's)term" 
  from fin[unfolded finite_constructor_form_pat_def tfvf finite_constructor_form_mp_def]
  have fin: "eqc \<in> set mp \<Longrightarrow> mp \<in> set fvf \<Longrightarrow> eqc \<noteq> [] \<and> (\<exists>\<iota>. finite_sort C \<iota> \<and> (\<forall>x \<in> set eqc. x : \<iota> in \<V> |` SS))" 
    for eqc mp by auto
  {
    fix eqc mp
    assume "mp \<in> set fvf" "eqc \<in> set mp" 
    with simpl[unfolded tfvf simplified_pp_def simplified_mp_def]  have "distinct (map ?Var eqc)" by auto
    hence "distinct eqc" unfolding distinct_map by auto
  } note dist_eqc = this
  define fvf' where "fvf' = map ( \<lambda> mp. zip [0..<length mp] mp) fvf" 
  have fvf': "fvf = map (map snd) fvf'" unfolding fvf'_def map_map o_def
    by (rule sym, rule map_idI, rule nth_equalityI, auto) 
  have dist1: "Ball (set fvf') (distinct \<circ> map fst)" unfolding fvf'_def
    by auto
  have dist2: "Ball (set (concat fvf')) (distinct \<circ> snd)" 
    unfolding fvf'_def
    by (auto simp: set_zip intro: dist_eqc)  
  define pp :: "(('f, nat \<times> 's) term \<times> ('f, nat) term) list list" where "pp = pat_of_var_form_list fvf'" 
  {
    fix mp i 
    assume mp: "mp \<in> set fvf" "i < length mp" 
    hence "mp ! i \<in> set mp" by auto
    from dist_eqc[OF mp(1) this] fin[OF this mp(1)] obtain \<iota>
      where dist: "distinct (mp ! i)" "finite_sort C \<iota>" "(\<forall>x\<in>set (mp ! i). x : \<iota> in \<V> |` SS)" by auto
    hence "\<forall> a b. (a,b) \<in> set (mp ! i) \<longrightarrow> b = \<iota> \<and> b \<in> S" unfolding hastype_def restrict_map_def 
      by (auto split: if_splits)
    with dist(1-2) have "distinct (mp ! i)" "\<exists> \<iota>. finite_sort C \<iota> \<and> (\<forall> x s. (x,s) \<in> set (mp ! i) \<longrightarrow> s = \<iota> \<and> s \<in> S)" 
      by blast+
  } note mpi = this

  have wf_pat: "wf_pat (pat_list pp)" unfolding pat_list_def pp_def pat_of_var_form_list_def using mpi(2)
    by (force simp: wf_pat_def wf_match_def match_of_var_form_list_def tvars_match_def fvf'_def set_zip)

  have var_form: "finite_var_form_pat C (pat_list pp)" unfolding pp_def fvf'_def 
    apply (auto simp: pat_list_def pat_of_var_form_list_def match_of_var_form_list_def finite_var_form_pat_def
      finite_var_form_match_def var_form_match_def set_zip)
    subgoal for mp x s y s' i using mpi(2)[of mp i] by blast
    subgoal for mp x s i using mpi(2)[of mp i] by blast
    done
  from pat_complete_via_idl_solver[OF var_form wf_pat pp_def dist1 dist2 small fvf']
  have "pat_complete C (pat_list pp) = fvf_solver solver fvf" unfolding fvf_solver_def .
  also have "pat_complete C (pat_list pp) = ((\<forall>f :\<^sub>s \<V> |` SS \<rightarrow> \<T>(C). Bex (pat_list pp) (match_complete_wrt f)))" 
    unfolding pat_complete_def 
  proof ((standard; intro allI impI), goal_cases)
    case (1 f)
    have "tvars_pat (pat_list pp) \<subseteq> SS" 
      using wf_pat unfolding wf_pat_def wf_match_def tvars_match_def tvars_pat_def by force
    with 1 have f: "f :\<^sub>s \<V> |` tvars_pat (pat_list pp) \<rightarrow> \<T>(C)" 
      by (auto simp: sorted_map_def tvars_pat_def restrict_map_def hastype_def)
    with 1 show "Bex (pat_list pp) (match_complete_wrt f)" by auto
  next
    case (2 f)
    define g where "g x = (if x \<in> tvars_pat (pat_list pp) then f x else \<sigma>g' x)" for x
    have g: "g :\<^sub>s \<V> |` SS \<rightarrow> \<T>(C)" using \<sigma>g' 2(2)
      by (auto simp: g_def sorted_map_def tvars_pat_def restrict_map_def hastype_def split: if_splits)
    with 2(1) obtain mp where mp: "mp \<in> pat_list pp" and match: "match_complete_wrt g mp" by auto
    have "match_complete_wrt g mp = match_complete_wrt f mp" unfolding match_complete_wrt_def
      apply (intro ex_cong1 ball_cong refl, clarsimp)
      subgoal for mu s t
        by (subst term_subst_eq[of s f g], insert mp, auto simp: g_def tvars_pat_def tvars_match_def)
      done
    with match show "Bex (pat_list pp) (match_complete_wrt f)" using mp by auto
  qed
  also have "\<dots> = simple_pat_complete C SS (set3 tfvf)" 
    unfolding simple_pat_complete_def pat_list_def tfvf set_map o_def pp_def fvf' 
      pat_of_var_form_list_def image_comp bex_simps
  proof (intro all_cong bex_cong refl)
    fix f mp
    assume "f :\<^sub>s (\<lambda>x. Some (snd x)) |` SS \<rightarrow> \<T>(C)" 
    assume "mp \<in> set fvf'" 
    with dist1 have dist1: "distinct (map fst mp)" by auto  
    show "match_complete_wrt f (set (match_of_var_form_list mp)) =
           simple_match_complete_wrt f {Var ` set (snd eqc) |. eqc \<in> set mp}"
      unfolding match_complete_wrt_def simple_match_complete_wrt_def ball_simps
    proof
      assume *: "\<forall>eqc \<in> set mp. UNIQ_subst f (Var ` set (snd eqc))" 
      define \<mu> where "\<mu> n = the_elem (Var ` set (the (map_of mp n)) \<cdot>\<^sub>s\<^sub>e\<^sub>t f)" for n
      show "\<exists>\<mu>. \<forall>(t, l)\<in>set (match_of_var_form_list mp). t \<cdot> f = l \<cdot> \<mu>" 
      proof (intro exI[of _ \<mu>], clarsimp simp: match_of_var_form_list_def)
        fix n eqc x s 
        assume eqc: "(n,eqc) \<in> set mp" and x: "(x,s) \<in> set eqc" 
        from * eqc have uniq: "UNIQ_subst f (Var ` set eqc)" by auto
        from eqc dist1 have the: "the (map_of mp n) = eqc" by simp
        hence \<mu>: "\<mu> n = the_elem (Var ` set eqc \<cdot>\<^sub>s\<^sub>e\<^sub>t f)" unfolding \<mu>_def by simp
        from Uniq_eq_the_elem[OF uniq[unfolded UNIQ_subst_def], folded this, of "f (x, s)"]
        show "f (x,s) = \<mu> n" using x by force
      qed
    next
      assume "\<exists>\<mu>. \<forall>(t, l)\<in>set (match_of_var_form_list mp). t \<cdot> f = l \<cdot> \<mu>" 
      then obtain \<mu> where \<mu>: "\<And> t l. (t, l) \<in> set (match_of_var_form_list mp) \<Longrightarrow> t \<cdot> f = l \<cdot> \<mu>" by auto
      show "\<forall>eqc\<in>set mp. UNIQ_subst f (Var ` set (snd eqc))" 
      proof (intro ballI, clarsimp)
        fix n eqc
        assume "(n, eqc) \<in> set mp" 
        hence "Var ` set eqc \<times> {Var n} \<subseteq> set (match_of_var_form_list mp)" 
          unfolding match_of_var_form_list_def by auto
        from \<mu>[OF set_mp[OF this]] have \<mu>: "x \<in> set eqc \<Longrightarrow> f x = \<mu> n" for x by fastforce
        thus "UNIQ_subst f (Var ` set eqc)" unfolding UNIQ_subst_alt_def by auto 
      qed
    qed
  qed
  finally show ?thesis by simp
qed

lemma fcf_solver_loop: assumes vars: "Ball (snd ` set P) (\<lambda> p. tvars_spat (set3 p) \<subseteq> {..<n} \<times> UNIV \<and> length p < k)"
  and prob: "spp_det_prob (mset4' P)" 
  and tags: "Ball (set (add4 P)) simpl_tag" 
shows "fcf_solver_loop solver n (add4 P) = spp_pat_complete (mset4' P)" 
  using vars prob tags
proof (induct P arbitrary: n rule: SN_induct[OF SN_inv_image[of _ mset4', OF SN_imp_SN_trancl[OF SN_spp_det_step]]])
  case (1 P n)
  note vars = 1(2)
  note prob = 1(3)
  note tags = 1(4)
  note IH = 1(1)
  note res = fcf_solver_loop.simps[of solver n "add4 P"]
  show ?case
  proof (cases P)
    case Nil
    thus ?thesis unfolding res by (auto simp: spp_pat_complete_def)
  next
    case (Cons tp ps)
    then obtain tag p where Cons: "P = (tag,p) # ps" by (cases tp, auto)
    hence P: "add4 P = (tag,add3 p) # add4 ps" by auto
    note res = res[unfolded P list.simps, folded P]
    from prob[unfolded Cons spp_det_prob_def] 
    have finp: "finite_constructor_form_pat (set3 p)" 
      using mset3_mset3'_set3[of p] by auto
    from vars[unfolded Cons] 
    have varsp: "tvars_spat (set3 p) \<subseteq> {..<n} \<times> UNIV \<and> length p < k" by auto
    from tags[unfolded P] have tag: "simpl_tag (tag,add3 p)"
      and tags_ps: "Ball (set (add4 ps)) simpl_tag" by auto
    show ?thesis
    proof (cases "full_step n (tag, add3 p)")
      case (Inl aps1)
      from full_step(1)[OF varsp finp tag refl Inl, of "mset4' ps"] Cons
      obtain ps1 where aps1: "aps1 = add4 ps1" and 
         steps: "(mset4' P, mset4' ps1 + mset4' ps) \<in> (\<Rrightarrow>\<^sub>s\<^sub>s)\<^sup>+" and
         varsps: "Ball (snd ` set ps1) (\<lambda> p'. tvars_spat (set3 p') \<subseteq> {..< n + m} \<times> UNIV \<and> length p' < k)" and
         tags: "Ball (set aps1) simpl_tag" 
        by auto
      from res[unfolded Inl sum.simps aps1]
      have res: "fcf_solver_loop solver n (add4 P) = fcf_solver_loop solver (n + m) (add4 (ps1 @ ps))" 
        by simp
      from varsps vars
      have vars: "\<forall>p\<in> snd ` set (ps1 @ ps). tvars_spat (set3 p) \<subseteq> {..<n+m} \<times> UNIV \<and> length p < k" 
        unfolding Cons by fastforce  
      from tags[unfolded aps1] tags_ps  
      have tags: "Ball (set (add4 (ps1 @ ps))) simpl_tag" by auto
      have "(P, ps1 @ ps) \<in> inv_image (\<Rrightarrow>\<^sub>s\<^sub>s\<^sup>+) mset4'" using steps by auto
      note IH = IH[OF this vars _ tags] 
      from steps have steps: "(mset4' P, mset4' (ps1 @ ps)) \<in> (\<Rrightarrow>\<^sub>s\<^sub>s)\<^sup>*" by simp
      from spp_det_steps_ms[OF this] prob 
      have prob: "spp_det_prob (mset4' (ps1 @ ps))"
        and sound: "spp_pat_complete (mset4' P) = spp_pat_complete (mset4' (ps1 @ ps))" by blast+
      show ?thesis 
        unfolding res
        unfolding IH[OF prob] 
        unfolding sound ..
    next
      case (Inr fvf)
      let ?fvf = "map (map (map (Var :: nat \<times> 's \<Rightarrow> ('f, nat \<times> 's)term))) fvf" 
      note res = res[unfolded Inr sum.simps]
      let ?new = "add_mset (mset3' ?fvf) (mset4' ps)" 
      from full_step(2)[OF varsp finp tag refl Inr, of "mset4' ps"] Cons
      have steps: "(mset4' P, ?new) \<in> (\<Rrightarrow>\<^sub>s\<^sub>s)\<^sup>*" 
       and simpl: "simplified_pp ?fvf" 
       and small: "(\<forall>x \<iota>. (x, \<iota>) \<in> set (concat (concat fvf)) \<longrightarrow> card_of_sort C \<iota> < k)" by auto
      from spp_det_steps_ms[OF steps] prob have "spp_det_prob ?new" 
        by (auto simp: o_def image_mset.compositionality)
      from this[unfolded spp_det_prob_def] have "finite_constructor_form_pat (mset3 (mset3' ?fvf))" by auto
      hence fin: "finite_constructor_form_pat (set3 ?fvf)" unfolding mset3_mset3'_set3 .
      have solver: "fvf_solver solver fvf = simple_pat_complete C SS (set3 ?fvf)" 
        by (rule fvf_solver[OF refl small fin simpl])
      have fvf: "(\<And> t. t \<in># \<Sum>\<^sub># (image_mset \<Sum>\<^sub># (mset3' ?fvf)) \<Longrightarrow> is_Var t)" 
        by auto
      show ?thesis
      proof (cases "fvf_solver solver fvf")
        case True
        from spp_fvf_succ[of "mset3' ?fvf", unfolded mset3_mset3'_set3, OF fvf True[unfolded solver]]
        have step: "(?new, mset4' ps) \<in> \<Rrightarrow>\<^sub>s\<^sub>s" by auto
        with steps have steps: "(mset4' P, mset4' ps) \<in> (\<Rrightarrow>\<^sub>s\<^sub>s)\<^sup>+" by auto
        from res True have res: "fcf_solver_loop solver n (add4 P) = fcf_solver_loop solver n (add4 ps)" by auto
        from vars have vars: "\<forall>p\<in>snd ` set ps. tvars_spat (set3 p) \<subseteq> {..<n} \<times> UNIV \<and> length p < k" 
          unfolding Cons by fastforce  
        have "(P, ps) \<in> inv_image (\<Rrightarrow>\<^sub>s\<^sub>s\<^sup>+) mset4'" using steps by auto
        note IH = IH[OF this vars _ tags_ps]
        from steps have steps: "(mset4' P, mset4' ps) \<in> (\<Rrightarrow>\<^sub>s\<^sub>s)\<^sup>*" ..
        from spp_det_steps_ms[OF this] prob 
        have prob: "spp_det_prob (mset4' ps)"
          and sound: "spp_pat_complete (mset4' P) = spp_pat_complete (mset4' ps)" 
          by (auto simp: o_def image_mset.compositionality)
        show ?thesis 
          unfolding res
          unfolding IH[OF prob] 
          unfolding sound ..
      next
        case False
        with res have res: "fcf_solver_loop solver n (add4 P) = False" by auto
        from False[unfolded solver] 
        have "\<not> simple_pat_complete C SS (set3 ?fvf)" by auto
        hence "\<not> spp_pat_complete ?new" unfolding spp_pat_complete_def o_def 
          using mset3_mset3'_set3[of ?fvf] by auto
        with spp_det_steps_ms[OF steps]
        show ?thesis unfolding res unfolding spp_pat_complete_def by auto
      qed
    qed
  qed
qed

lemma fcf_solver_alg: assumes vars: "tvars_spat (set3 p) \<subseteq> {..<n} \<times> UNIV"
  and k: "length p < k"
  and fin: "finite_constructor_form_pat (set3 p)"  
shows "fcf_solver_alg solver n p = simple_pat_complete C SS (set3 p)" 
proof -
  have "fcf_solver_alg solver n p = fcf_solver_loop solver n (add4 [(False,p)])" 
    unfolding fcf_solver_alg_def by simp
  also have "\<dots> = spp_pat_complete ({#mset3' p#})" using mset3_mset3'_set3[of p]
    by (subst fcf_solver_loop, insert vars fin k, auto)
  also have "\<dots> = simple_pat_complete C SS (set3 p)" using mset3_mset3'_set3[of p]
    unfolding spp_pat_complete_def by auto
  finally show ?thesis .
qed

lemma fcf_solver_alg': "fcf_solver k (fcf_solver_alg solver)" 
  unfolding fcf_solver_def using fcf_solver_alg by auto
end
end 

(* code equations *)
context pattern_completeness_context
begin

lemmas fcf_solver_code_eqns = 
  fcf_solver_alg_def
  fcf_solver_loop.simps
  fvf_solver_def
  full_step_def
  simplify_tpp.simps
  simplify_pp.simps
  simplify_mp_def
  simplify_mp_main.simps
  add_sort.simps
  inst_list_def[unfolded s\<tau>s_list_def s\<tau>c_def map_map]
  large_sort_impl_def
  large_sort_impl_main_def

end

declare pattern_completeness_context.fcf_solver_code_eqns[code]

end