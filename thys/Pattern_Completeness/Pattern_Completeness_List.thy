section \<open>A List-Based Implementation to Decide Pattern Completeness\<close>

theory Pattern_Completeness_List
  imports 
    Pattern_Completeness_Multiset
    Compute_Nonempty_Infinite_Sorts
    Finite_IDL_Solver_Interface
    "HOL-Library.AList" 
    "HOL-Library.Mapping" 
    Singleton_List
begin

subsection \<open>Definition of Algorithm\<close>

text \<open>We refine the non-deterministic multiset based implementation
  to a deterministic one which uses lists as underlying data-structure.
  For matching problems we distinguish several different shapes.\<close>

type_synonym ('a,'b)alist = "('a \<times> 'b)list"
type_synonym ('f,'v,'s)match_problem_list = "(('f,nat \<times> 's)term \<times> ('f,'v)term) list" \<comment> \<open>mp with arbitrary pairs\<close>
type_synonym ('f,'v,'s)match_problem_lx = "((nat \<times> 's) \<times> ('f,'v)term) list"  \<comment> \<open>mp where left components are variable\<close>
type_synonym ('f,'v,'s)match_problem_rx = "('v,('f,nat \<times> 's)term list) alist \<times> bool" \<comment> \<open>mp where right components are variables\<close>
type_synonym ('f,'v,'s)match_problem_fvf = "('v,(nat \<times> 's) list) alist" 
type_synonym ('f,'v,'s)match_problem_lr = "('f,'v,'s)match_problem_lx \<times> ('f,'v,'s)match_problem_rx" \<comment> \<open>a partitioned mp\<close>
type_synonym ('f,'v,'s)pat_problem_list = "('f,'v,'s)match_problem_list list" 
type_synonym ('f,'v,'s)pat_problem_lr = "('f,'v,'s)match_problem_lr list" 
type_synonym ('f,'v,'s)pat_problem_lx = "('f,'v,'s)match_problem_lx list" 
type_synonym ('f,'v,'s)pat_problem_fvf = "('f,'v,'s)match_problem_fvf list" 
type_synonym ('f,'v,'s)pats_problem_list = "('f,'v,'s)pat_problem_list list" 
type_synonym ('f,'v,'s)pat_problem_set_impl = "(('f,nat \<times> 's)term \<times> ('f,'v)term) list list" 

definition lvars_mp :: "('f,'v,'s)match_problem_mset \<Rightarrow> 'v set" where
  "lvars_mp mp = (\<Union> (vars ` snd ` mp_mset mp))" 

definition vars_mp_mset :: "('f,'v,'s)match_problem_mset \<Rightarrow> 'v multiset" where
  "vars_mp_mset mp = sum_mset (image_mset (vars_term_ms o snd) mp)" 

(* left-linear matching problems *)
definition ll_mp :: "('f,'v,'s)match_problem_mset \<Rightarrow> bool" where
  "ll_mp mp = (\<forall> x. count (vars_mp_mset mp) x \<le> 1)"  

definition ll_pp :: "('f,'v,'s)pat_problem_list \<Rightarrow> bool" where
  "ll_pp p = (\<forall> mp \<in> set p. ll_mp (mset mp))"  

definition lvars_pp :: "('f,'v,'s)pat_problem_mset \<Rightarrow> 'v set" where
  "lvars_pp pp = (\<Union> (lvars_mp ` set_mset pp))" 

abbreviation mp_list :: "('f,'v,'s)match_problem_list \<Rightarrow> ('f,'v,'s)match_problem_mset" 
  where "mp_list \<equiv> mset" 

abbreviation mp_lx :: "('f,'v,'s)match_problem_lx \<Rightarrow> ('f,'v,'s)match_problem_list" 
  where "mp_lx \<equiv> map (map_prod Var id)" 

definition mp_rx :: "('f,'v,'s)match_problem_rx \<Rightarrow> ('f,'v,'s)match_problem_mset"
  where "mp_rx mp = mset (List.maps (\<lambda> (x,ts). map (\<lambda> t. (t,Var x)) ts) (fst mp))" 

definition mp_rx_list :: "('f,'v,'s)match_problem_rx \<Rightarrow> ('f,'v,'s)match_problem_list"
  where "mp_rx_list mp = List.maps (\<lambda> (x,ts). map (\<lambda> t. (t,Var x)) ts) (fst mp)" 

definition mp_lr :: "('f,'v,'s)match_problem_lr \<Rightarrow> ('f,'v,'s)match_problem_mset"
  where "mp_lr pair = (case pair of (lx,rx) \<Rightarrow> mp_list (mp_lx lx) + mp_rx rx)" 

definition mp_lr_list :: "('f,'v,'s)match_problem_lr \<Rightarrow> ('f,'v,'s)match_problem_list"
  where "mp_lr_list pair = (case pair of (lx,rx) \<Rightarrow> mp_lx lx @ mp_rx_list rx)" 

definition pat_lr :: "('f,'v,'s)pat_problem_lr \<Rightarrow> ('f,'v,'s)pat_problem_mset"
  where "pat_lr ps = mset (map mp_lr ps)" 

definition pat_lx :: "('f,'v,'s)pat_problem_lx \<Rightarrow> ('f,'v,'s)pat_problem_mset"
  where "pat_lx ps = mset (map (mp_list o mp_lx) ps)" 

definition pat_mset_list :: "('f,'v,'s)pat_problem_list \<Rightarrow> ('f,'v,'s)pat_problem_mset"
  where "pat_mset_list ps = mset (map mp_list ps)" 

definition pat_list :: "('f,'v,'s)pat_problem_list \<Rightarrow> ('f,'v,'s)pat_problem_set"
  where "pat_list ps = set ` set ps" 

abbreviation pats_mset_list :: "('f,'v,'s)pats_problem_list \<Rightarrow> ('f,'v,'s)pats_problem_mset" 
  where "pats_mset_list \<equiv> mset o map pat_mset_list" 
 
definition subst_match_problem_list :: "('f,nat \<times> 's)subst \<Rightarrow> ('f,'v,'s)match_problem_list \<Rightarrow> ('f,'v,'s)match_problem_list" where
  "subst_match_problem_list \<tau> = map (subst_left \<tau>)" 

definition subst_pat_problem_list :: "('f,nat \<times> 's)subst \<Rightarrow> ('f,'v,'s)pat_problem_list \<Rightarrow> ('f,'v,'s)pat_problem_list" where
  "subst_pat_problem_list \<tau> = map (subst_match_problem_list \<tau>)" 

definition match_var_impl :: "('f,'v,'s)match_problem_lr \<Rightarrow> 'v list \<times> ('f,'v,'s)match_problem_lr" where
  "match_var_impl mp = (case mp of (xl,(rx,b)) \<Rightarrow>
     let xs = remdups (List.maps (vars_term_list o snd) xl)
     in (xs,(xl,(filter (\<lambda> (x,ts). tl ts \<noteq> [] \<or> x \<in> set xs) rx),b)))" 

definition find_var :: "bool \<Rightarrow> ('f,'v,'s)match_problem_lr list \<Rightarrow> _" where 
  "find_var improved p = (case List.maps (\<lambda> (lx,_). lx) p of
      (x,t) # _ \<Rightarrow> Some x
    | [] \<Rightarrow> if improved then (let flat_mps = List.maps (fst o snd) p in 
       (map_option (\<lambda> (x,ts). case find is_Var ts of Some (Var x) \<Rightarrow> x)
       (find (\<lambda> rx. \<exists> t \<in> set (snd rx). is_Fun t) flat_mps)))
       else Some (let (_,rx,b) = hd p
         in case hd rx of (x, s # t # _) \<Rightarrow> hd (the (conflicts s t))))" 

definition empty_lr :: "('f,'v,'s)match_problem_lr \<Rightarrow> bool" where
  "empty_lr mp = (case mp of (lx,rx,_) \<Rightarrow> lx = [] \<and> rx  = [])" 

fun zipAll :: "'a list \<Rightarrow> 'b list list \<Rightarrow> ('a \<times> 'b list) list" where
  "zipAll [] _ = []" 
| "zipAll (x # xs) yss = (x, map hd yss) # zipAll xs (map tl yss)" 

datatype ('f,'v,'s)pat_impl_result = Incomplete
  | New_Problems "nat \<times> nat \<times> ('f,'v,'s)pat_problem_list list" 
  | Fin_Var_Form "('f,'v,'s)pat_problem_fvf" 

text \<open>Transforming finite variable forms:\<close>

definition "tvars_match_list = remdups \<circ> concat \<circ> map (var_list_term \<circ> fst)"

definition "tvars_pat_list = remdups \<circ> concat \<circ> map tvars_match_list"

definition var_form_of_match_rx :: "('f,'v,'s)match_problem_rx \<Rightarrow> ('v \<times> (nat \<times> 's) list) list" where
  "var_form_of_match_rx = map (map_prod id (map the_Var)) o fst"

definition match_of_var_form_list where
  "match_of_var_form_list mpv = concat [[(Var v, Var x). v \<leftarrow> vs]. (x,vs) \<leftarrow> mpv]"

definition var_form_of_pat_rx where
  "var_form_of_pat_rx = map var_form_of_match_rx"

definition pat_of_var_form_list where
  "pat_of_var_form_list = map match_of_var_form_list"

lemma size_zip[termination_simp]: "length ts = length ls \<Longrightarrow> size_list (\<lambda>p. size (snd p)) (zip ts ls) 
  < Suc (size_list size ls)"  
  by (induct ts ls rule: list_induct2, auto)

fun match_decomp_lin_impl :: "('f,'v,'s)match_problem_list \<Rightarrow> ('f,'v,'s)match_problem_lx option" where
  "match_decomp_lin_impl [] = Some []"
| "match_decomp_lin_impl ((Fun f ts, Fun g ls) # mp) = (if (f,length ts) = (g,length ls) then 
     match_decomp_lin_impl (zip ts ls @ mp) else None)" 
| "match_decomp_lin_impl ((Var x, Fun g ls) # mp) = (map_option (Cons (x, Fun g ls)) (match_decomp_lin_impl mp))" 
| "match_decomp_lin_impl ((t, Var y) # mp) = match_decomp_lin_impl mp" 

fun pat_inner_lin_impl :: "('f,'v,'s)pat_problem_list \<Rightarrow> ('f,'v,'s)pat_problem_lx \<Rightarrow> ('f,'v,'s)pat_problem_lx option" where
  "pat_inner_lin_impl [] pd = Some pd" 
| "pat_inner_lin_impl (mp # p) pd = (case match_decomp_lin_impl mp of 
     None \<Rightarrow> pat_inner_lin_impl p pd
   | Some mp' \<Rightarrow> if mp' = [] then None
       else pat_inner_lin_impl p (mp' # pd))" 

definition "bounds_list bnd cnf = (let vars = remdups (concat (concat cnf))
  in map (\<lambda> v. (v, int (bnd v) - 1)) vars)" 

fun pairs_of_list where 
  "pairs_of_list (x # y # xs) = (x,y) # pairs_of_list (y # xs)" 
| "pairs_of_list _ = []" 

lemma set_pairs_of_list: "set (pairs_of_list xs) = { (xs ! i, xs ! (Suc i)) | i. Suc i < length xs}" 
proof (induct xs rule: pairs_of_list.induct)
  case (1 x y xs)
  define n where "n = length xs" 
  have id: "{f i |i. Suc i < length (x # y # xs)}
    = insert (f 0) {f (Suc i) |i. Suc i < length (y # xs)}" for f :: "nat \<Rightarrow> 'a \<times> 'a"  
    unfolding list.size n_def[symmetric] 
    apply auto
    subgoal for a b i by (cases i, auto)
    done
  show ?case unfolding pairs_of_list.simps set_simps 1 id by auto
qed auto

lemma diff_pairs_of_list: "(\<exists> x \<in> set xs. \<exists> y \<in> set xs. f x \<noteq> f y) \<longleftrightarrow> 
  (\<exists> (x,y) \<in> set (pairs_of_list xs). f x \<noteq> f y)" (is "?l = ?r")
proof
  assume ?r
  from this[unfolded set_pairs_of_list] obtain i where i: "Suc i < length xs" 
    and diff: "f (xs ! i) \<noteq> f (xs ! (Suc i))" by auto
  from i have "xs ! i \<in> set xs" "xs ! (Suc i) \<in> set xs" by auto
  with diff show ?l by auto
next
  assume ?l
  show ?r
  proof (rule ccontr)
    let ?n = "length xs" 
    assume "\<not> ?r" 
    hence eq: "\<And> i. Suc i < ?n \<Longrightarrow> f (xs ! i) = f (xs ! (Suc i))" by (auto simp: set_pairs_of_list)
    have eq: "i < ?n \<Longrightarrow> f (xs ! i) = f (xs ! 0)" for i
      by (induct i, insert eq, auto)
    hence "\<And> i j. i < ?n \<Longrightarrow> j < ?n \<Longrightarrow> f (xs ! i) = f (xs ! j)" by auto
    with \<open>?l\<close> show False unfolding set_conv_nth by auto
  qed
qed

definition "dist_pairs_list cnf = map (List.maps pairs_of_list) cnf" 

context pattern_completeness_context
begin


text \<open>insert an element into the part of the mp that stores pairs of form (t,x) for variables x.
   Internally this is represented as maps (assoc lists) from x to terms t1,t2,... so that linear terms are easily
   identifiable. Duplicates will be removed and clashes will be immediately be detected and result in None.\<close>
definition insert_rx :: "('f,nat \<times> 's)term \<Rightarrow> 'v \<Rightarrow> ('f,'v,'s)match_problem_rx \<Rightarrow> ('f,'v,'s)match_problem_rx option" where
  "insert_rx t x rxb = (case rxb of (rx,b) \<Rightarrow> (case map_of rx x of 
    None \<Rightarrow> Some (((x,[t]) # rx, b))
  | Some ts \<Rightarrow> (case those (map (conflicts t) ts)
       of None \<Rightarrow> None \<comment> \<open>clash\<close>
        | Some cs \<Rightarrow> if [] \<in> set cs then Some rxb \<comment> \<open>empty conflict means (t,x) was already part of rxb\<close>
          else Some ((AList.update x (t # ts) rx, b \<or> (\<exists> y \<in> set (concat cs). inf_sort (snd y))))
       )))"

text \<open>Decomposition applies decomposition, duplicate and clash rule to classify all remaining problems 
  as being of kind (x,f(l1,..,ln)) or (t,x).\<close>
fun decomp_impl :: "('f,'v,'s)match_problem_list \<Rightarrow> ('f,'v,'s)match_problem_lr option" where
  "decomp_impl [] = Some ([],([],False))"
| "decomp_impl ((Fun f ts, Fun g ls) # mp) = (if (f,length ts) = (g,length ls) then 
     decomp_impl (zip ts ls @ mp) else None)" 
| "decomp_impl ((Var x, Fun g ls) # mp) = (case decomp_impl mp of Some (lx,rx) \<Rightarrow> Some ((x,Fun g ls) # lx,rx) 
       | None \<Rightarrow> None)" 
| "decomp_impl ((t, Var y) # mp) = (case decomp_impl mp of Some (lx,rx) \<Rightarrow> 
       (case insert_rx t y rx of Some rx' \<Rightarrow> Some (lx,rx') | None \<Rightarrow> None)
       | None \<Rightarrow> None)" 

definition pat_lin_impl :: "nat \<Rightarrow> ('f,'v,'s)pat_problem_list \<Rightarrow> ('f,'v,'s)pat_problem_list list option" where
  "pat_lin_impl n p = (case pat_inner_lin_impl p [] of None \<Rightarrow> Some []
      | Some p' \<Rightarrow> if p' = [] then None 
        else (let x = fst (hd (hd p')); p'l = map mp_lx p' in 
          Some (map (\<lambda> \<tau>. subst_pat_problem_list \<tau> p'l) (\<tau>s_list n x))))" 

partial_function (tailrec) pats_lin_impl :: "nat \<Rightarrow> ('f,'v,'s)pats_problem_list \<Rightarrow> bool" where
  "pats_lin_impl n ps = (case ps of [] \<Rightarrow> True
     | p # ps1 \<Rightarrow> (case pat_lin_impl n p of 
         None \<Rightarrow> False
       | Some ps2 \<Rightarrow> pats_lin_impl (n + m) (ps2 @ ps1)))"

definition match_steps_impl :: "('f,'v,'s)match_problem_list \<Rightarrow> ('v list \<times> ('f,'v,'s)match_problem_lr) option" where
  "match_steps_impl mp = (map_option match_var_impl (decomp_impl mp))" 

definition pat_complete_lin_impl :: "('f,'v,'s)pats_problem_list \<Rightarrow> bool" where
  "pat_complete_lin_impl ps = (let 
      n = Suc (max_list (List.maps (map fst o vars_term_list o fst) (concat (concat ps))))
     in pats_lin_impl n ps)" 

context 
  fixes
  CC :: "'f \<times> 's list \<Rightarrow> 's option" and  
  renNat :: "nat \<Rightarrow> 'v" and 
  renVar :: "'v \<Rightarrow> 'v" and
  fidl_solver :: "((nat \<times> 's) \<times> int) list \<times> ((nat \<times> 's) \<times> (nat \<times> 's)) list list \<Rightarrow> bool" 
begin

partial_function (tailrec) decomp'_main_loop where 
  "decomp'_main_loop n xs list out = (case list of 
      [] \<Rightarrow> (n, out) \<comment> \<open>one might change to (rev out) in order to preserve the order\<close>
    | ((x,ts) # rxs) \<Rightarrow> (if tl ts = [] \<or> (\<exists> t \<in> set ts. is_Var t) \<or> x \<in> set xs
     then decomp'_main_loop n xs rxs ((x,ts) # out)
     else let l = length (args (hd ts));
              fresh = map renNat [n ..< n + l];
              new = zipAll fresh (map args ts);
              cleaned = filter (\<lambda> (y,ts'). tl ts' \<noteq> []) (map (\<lambda> (y,ts'). (y, remdups ts')) new)
           in decomp'_main_loop (n + l) xs (cleaned @ rxs) out))" 

definition decomp'_impl where 
  "decomp'_impl n xs mp = (case mp of 
     (xl,(rx,b)) \<Rightarrow> case decomp'_main_loop n xs rx [] of
     (n', rx') \<Rightarrow> (n', (xl,(rx',b))))" 

(* there needs to be a decision, which rules to prioritize;
   currently decompose' is given a low priority, in particular,
   it is applied after the instantiate rule because of the condition
   xl = [], i.e., only if inst is not applicable.
   Reason: decompose' is only required for non-linear systems  *)
definition apply_decompose' :: "('f,'v,'s)match_problem_lr \<Rightarrow> bool"
  where "apply_decompose' mp = (improved \<and> (case mp of (xl,(rx,b)) \<Rightarrow> (\<not> b \<and> xl = [])))" 

definition match_decomp'_impl :: "nat \<Rightarrow> ('f,'v,'s)match_problem_list \<Rightarrow> (nat \<times> ('f,'v,'s)match_problem_lr) option" where
  "match_decomp'_impl n mp = map_option (\<lambda> (xs,mp). 
    if apply_decompose' mp 
    then decomp'_impl n xs mp else (n, mp)) (match_steps_impl mp)" 

fun pat_inner_impl :: "nat \<Rightarrow> ('f,'v,'s)pat_problem_list \<Rightarrow> ('f,'v,'s)pat_problem_lr \<Rightarrow> (nat \<times> ('f,'v,'s)pat_problem_lr) option" where
  "pat_inner_impl n [] pd = Some (n, pd)" 
| "pat_inner_impl n (mp # p) pd = (case match_decomp'_impl n mp of 
     None \<Rightarrow> pat_inner_impl n p pd
   | Some (n',mp') \<Rightarrow> if empty_lr mp' then None
       else pat_inner_impl n' p (mp' # pd))" 

definition pat_impl :: "nat \<Rightarrow> nat \<Rightarrow> ('f,'v,'s)pat_problem_list \<Rightarrow> ('f,'v,'s)pat_impl_result" where
  "pat_impl n nl p = (case pat_inner_impl nl p [] of None \<Rightarrow> New_Problems (n,nl,[])
      | Some (nl',p') \<Rightarrow> (case partition (\<lambda> mp. snd (snd mp)) p' of
         (ivc,no_ivc) \<Rightarrow> if no_ivc = [] then Incomplete \<comment> \<open>detected inf-var-conflict (or empty mp)\<close>
        else (if improved \<and> ivc \<noteq> [] \<and> (\<forall> mp \<in> set no_ivc. fst mp = []) then 
          New_Problems (n, nl', [map mp_lr_list (filter \<comment> \<open>inf-var-conflict' + match-clash-sort\<close>
            ( \<lambda> mp. \<forall> xts \<in> set (fst (snd mp)). is_singleton_list (map (\<T>(CC,\<V>)) (snd xts))) no_ivc)])
        else (case find_var improved no_ivc of Some x \<Rightarrow> let p'l = map mp_lr_list p'           
         in
           New_Problems (n + m, nl', map (\<lambda> \<tau>. subst_pat_problem_list \<tau> p'l) (\<tau>s_list n x))
         | None \<Rightarrow> Fin_Var_Form (map (map (map_prod id (map the_Var)) o fst o snd) no_ivc)))))" 

partial_function (tailrec) pats_impl :: "nat \<Rightarrow> nat \<Rightarrow> ('f,'v,'s)pats_problem_list \<Rightarrow> bool" where
  "pats_impl n nl ps = (case ps of [] \<Rightarrow> True
     | p # ps1 \<Rightarrow> (case pat_impl n nl p of 
         Incomplete \<Rightarrow> False
       | Fin_Var_Form p' \<Rightarrow>
         let bnd = (cd_sort \<circ> snd); cnf = (map (map snd) p')
         in if fidl_solver (bounds_list bnd cnf, dist_pairs_list cnf) then False else 
            pats_impl n nl ps1
       | New_Problems (n',nl',ps2) \<Rightarrow> pats_impl n' nl' (ps2 @ ps1)))"

definition pat_complete_impl :: "('f,'v,'s)pats_problem_list \<Rightarrow> bool" where
  "pat_complete_impl ps = (let 
      n = Suc (max_list (List.maps (map fst o vars_term_list o fst) (concat (concat ps))));
      nl = 0;
      ps' = if improved then map (map (map (apsnd (map_vars renVar)))) ps else ps
     in pats_impl n nl ps')" 
end
end

definition renaming_funs :: "(nat \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool" where
  "renaming_funs rn rx = (inj rn \<and> inj rx \<and> range rn \<inter> range rx = {})" 

lemmas pat_complete_impl_code = 
  pattern_completeness_context.pat_complete_impl_def
  pattern_completeness_context.pats_impl.simps
  pattern_completeness_context.pat_impl_def
  pattern_completeness_context.\<tau>s_list_def
  pattern_completeness_context.apply_decompose'_def
  pattern_completeness_context.decomp'_main_loop.simps
  pattern_completeness_context.decomp'_impl_def
  pattern_completeness_context.insert_rx_def
  pattern_completeness_context.decomp_impl.simps
  pattern_completeness_context.match_decomp'_impl_def
  pattern_completeness_context.match_steps_impl_def
  pattern_completeness_context.pat_inner_impl.simps
  pattern_completeness_context.pat_lin_impl_def
  pattern_completeness_context.pats_lin_impl.simps
  pattern_completeness_context.pat_complete_lin_impl_def

declare pat_complete_impl_code[code]


subsection \<open>Partial Correctness of the Implementation\<close>

text \<open>TODO: move\<close>

lemma mset_sum_reindex: "(\<Sum>x\<in>#A. image_mset (f x) B) = (\<Sum>i\<in>#B. {#f x i. x \<in># A#})"
proof (induct A)
  case (add x A)
  show ?case 
    by (simp add: add) 
     (smt (verit, del_insts) add.commute add_mset_add_single image_mset_cong sum_mset.distrib
        sum_mset_singleton_mset)
qed auto

lemma vars_mp_mset_add: "vars_mp_mset (mp + mp') = vars_mp_mset mp + vars_mp_mset mp'" 
  unfolding vars_mp_mset_def by auto


text \<open>zipAll\<close>

lemma zipAll: assumes "length as = n" 
  and "\<And> bs. bs \<in> set bss \<Longrightarrow> length bs = n" 
shows "zipAll as bss = map (\<lambda> i. (as ! i, map (\<lambda> bs. bs ! i) bss)) [0..<n]" 
  using assms 
proof (induct as arbitrary: n bss)
  case (Cons a as sn bss)
  then obtain n where sn: "sn = Suc n" by auto
  let ?tbss = "map tl bss" 
  from Cons(2-) sn have prems: "length as = n" "\<And> bs. bs \<in> set ?tbss \<Longrightarrow> length bs = n" 
    by auto
  from Cons(2-) sn have hd: "bs \<in> set bss \<Longrightarrow> hd bs = bs ! 0" for bs by (cases bs) force+
  from Cons(2-) sn have tl: "bs \<in> set bss \<Longrightarrow> tl bs ! i = bs ! Suc i" for bs i by (cases bs) force+
  note IH = Cons(1)[OF prems, of ?tbss]
  have id: "[0..<sn] = 0 # map Suc [0..<n]" unfolding sn upt_0_Suc_Cons ..
  show ?case unfolding id zipAll.simps list.simps map_map o_def
    by (subst IH, insert hd tl, auto)
qed simp

text \<open>We prove that the list-based implementation is 
  a refinement of the multiset-based one.\<close>

lemma mset_concat_union:
  "mset (concat xs) = \<Sum>\<^sub># (mset (map mset xs))"
  by (induct xs, auto simp: union_commute)

lemma in_map_mset[intro]:
  "a \<in># A \<Longrightarrow> f a \<in># image_mset f A"
  unfolding in_image_mset by simp


lemma mset_update: "map_of xs x = Some y \<Longrightarrow>
  mset (AList.update x z xs) = (mset xs - {# (x,y) #}) + {# (x,z) #}" 
  by (induction xs, auto)

lemma set_update: "map_of xs x = Some y \<Longrightarrow> distinct (map fst xs) \<Longrightarrow> 
  set (AList.update x z xs) = insert (x,z) (set xs - {(x,y)})" 
  by (induction xs, auto)

lemma mp_rx_append: "mp_rx (xs @ ys, b) = mp_rx (xs,b) + mp_rx (ys,b)" 
  unfolding mp_rx_def List.maps_def by auto

lemma mp_rx_Cons: "mp_rx (p # xs, b) = mp_list (case p of (x, ts) \<Rightarrow> map (\<lambda>t. (t, Var x)) ts) 
  + mp_rx (xs,b)" 
  unfolding mp_rx_def List.maps_def by auto

lemma set_tvars_match_list: "set (tvars_match_list mp) = tvars_match (set mp)"
  by (auto simp: tvars_match_list_def tvars_match_def)

lemma set_tvars_pat_list: "set (tvars_pat_list pp) = tvars_pat (pat_list pp)"
  by (simp add: tvars_pat_list_def tvars_pat_def set_tvars_match_list pat_list_def)

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

context pattern_completeness_context_with_assms
begin

text \<open>Various well-formed predicates for intermediate results\<close>

definition wf_ts :: "('f, nat \<times> 's) term list \<Rightarrow> bool"  where 
  "wf_ts ts = (ts \<noteq> [] \<and> distinct ts \<and> (\<forall> j < length ts. \<forall> i < j. conflicts (ts ! i) (ts ! j) \<noteq> None))" 

definition wf_ts2 :: "('f, nat \<times> 's) term list \<Rightarrow> bool"  where 
  "wf_ts2 ts = (length ts \<ge> 2 \<and> distinct ts \<and> (\<forall> j < length ts. \<forall> i < j. conflicts (ts ! i) (ts ! j) \<noteq> None))" 

definition wf_ts3 :: "('f, nat \<times> 's) term list \<Rightarrow> bool"  where 
  "wf_ts3 ts = (\<exists> t \<in> set ts. is_Var t)" 

definition wf_lx :: "('f,'v,'s)match_problem_lx \<Rightarrow> bool" where
  "wf_lx lx = (Ball (snd ` set lx) is_Fun)" 

definition wf_rx :: "('f,'v,'s)match_problem_rx \<Rightarrow> bool" where
  "wf_rx rx = (distinct (map fst (fst rx)) \<and> (Ball (snd ` set (fst rx)) wf_ts) \<and> snd rx = inf_var_conflict (set_mset (mp_rx rx)))" 

definition wf_rx2 :: "('f,'v,'s)match_problem_rx \<Rightarrow> bool" where
  "wf_rx2 rx = (distinct (map fst (fst rx)) \<and> (Ball (snd ` set (fst rx)) wf_ts2) \<and> snd rx = inf_var_conflict (set_mset (mp_rx rx)))" 

definition wf_rx3 :: "('f,'v,'s)match_problem_rx \<Rightarrow> bool" where
  "wf_rx3 rx = (wf_rx2 rx \<and> (improved \<longrightarrow> snd rx \<or> (Ball (snd ` set (fst rx)) wf_ts3)))" 

definition wf_lr :: "('f,'v,'s)match_problem_lr \<Rightarrow> bool"
  where "wf_lr pair = (case pair of (lx,rx) \<Rightarrow> wf_lx lx \<and> wf_rx rx)" 

definition wf_lr2 :: "('f,'v,'s)match_problem_lr \<Rightarrow> bool"
  where "wf_lr2 pair = (case pair of (lx,rx) \<Rightarrow> wf_lx lx \<and> (if lx = [] then wf_rx2 rx else wf_rx rx))" 

definition wf_lr3 :: "('f,'v,'s)match_problem_lr \<Rightarrow> bool"
  where "wf_lr3 pair = (case pair of (lx,rx) \<Rightarrow> wf_lx lx \<and> (if lx = [] then wf_rx3 rx else wf_rx rx))" 

definition wf_pat_lr :: "('f,'v,'s)pat_problem_lr \<Rightarrow> bool" where
  "wf_pat_lr mps = (Ball (set mps) (\<lambda> mp. wf_lr3 mp \<and> \<not> empty_lr mp))" 

definition wf_pat_lx :: "('f,'v,'s)pat_problem_lx \<Rightarrow> bool" where
  "wf_pat_lx mps = (Ball (set mps) (\<lambda> mp. ll_mp (mp_list (mp_lx mp)) \<and> wf_lx mp \<and> mp \<noteq> []))" 

lemma wf_rx_mset: assumes "mset rx = mset rx'" 
  shows "wf_rx (rx,b) = wf_rx (rx',b)" 
proof -
  from assms have set: "set rx = set rx'" by (metis mset_eq_setD)
  show ?thesis
    unfolding wf_rx_def fst_conv snd_conv mp_rx_def set
    apply (intro conj_cong refl mset_eq_imp_distinct_iff 
      arg_cong2[of _ _ _ _ "(=)"]
      arg_cong[of _ _ inf_var_conflict])
    subgoal using assms by simp
    subgoal by (auto simp: List.maps_def set)
    done
qed
    

lemma wf_rx2_mset: assumes "mset rx = mset rx'" 
  shows "wf_rx2 (rx,b) = wf_rx2 (rx',b)" 
proof -
  from assms have set: "set rx = set rx'" by (metis mset_eq_setD)
  show ?thesis
    unfolding wf_rx2_def fst_conv snd_conv mp_rx_def set
    apply (intro conj_cong refl mset_eq_imp_distinct_iff 
      arg_cong2[of _ _ _ _ "(=)"]
      arg_cong[of _ _ inf_var_conflict])
    subgoal using assms by simp
    subgoal by (auto simp: List.maps_def set)
    done
qed


lemma wf_lr2_mset: assumes "mset rx = mset rx'" 
shows "wf_lr2 (lx,(rx,b)) = wf_lr2 (lx,(rx',b))" 
  using assms
  unfolding wf_lr2_def split wf_rx2_mset[OF assms] wf_rx_mset[OF assms]
  by simp

lemma mp_lr_mset: assumes "mset rx = mset rx'" 
  shows "mp_lr (lx,(rx,b)) = mp_lr (lx,(rx',b))" 
  unfolding mp_lr_def split mp_rx_def List.maps_def mset_concat_union using assms 
  by auto

lemma mp_list_lr: "mp_list (mp_lr_list mp) = mp_lr mp" 
  unfolding mp_lr_list_def mp_lr_def
  by (cases mp, auto simp: mp_rx_def mp_rx_list_def)

lemma pat_mset_list_lr: "pat_mset_list (map mp_lr_list pp) = pat_lr pp" 
  unfolding pat_lr_def pat_mset_list_def map_map o_def mp_list_lr by simp


lemma size_term_0[simp]: "size (t :: ('f,'v)term) > 0" 
  by (cases t, auto)

lemma wf_ts_no_conflict_alt_def: "(\<forall> j < length ts. \<forall> i < j. conflicts (ts ! i) (ts ! j) \<noteq> None)
  \<longleftrightarrow> (\<forall> s t. s \<in> set ts \<longrightarrow> t \<in> set ts \<longrightarrow> conflicts s t \<noteq> None)" (is "?l = ?r")
proof
  assume ?l
  note l = this[rule_format]
  show ?r
  proof (intro allI impI)
    fix s t
    assume "s \<in> set ts" "t \<in> set ts" 
    then obtain i j where ij: "i < length ts" "j < length ts" 
      and st: "s = ts ! i" "t = ts ! j" unfolding set_conv_nth by auto  
    then consider (lt) "i < j" | (eq) "i = j" | (gt) "j < i" by linarith
    thus "conflicts s t \<noteq> None" 
    proof cases
      case lt
      show ?thesis using l[OF ij(2) lt] unfolding st by auto
    next
      case eq
      show ?thesis unfolding st eq by simp
    next
      case gt
      show ?thesis using l[OF ij(1) gt] conflicts_sym[of s t] unfolding st
        by (simp add: option.rel_sel)
    qed
  qed
next
  assume ?r
  note r = this[rule_format]
  show ?l
  proof (intro allI impI)
    fix j i 
    assume "j < length ts" "i < j" 
    hence "ts ! i \<in> set ts" "ts ! j \<in> set ts" by (auto simp: set_conv_nth)
    from r[OF this] show "conflicts (ts ! i) (ts ! j) \<noteq> None" 
      by auto
  qed
qed
  
  

text \<open>Continue with properties of the sub-algorithms\<close>

lemma insert_rx: assumes res: "insert_rx t x rxb = res"
  and wf: "wf_rx rxb" 
  and mp: "mp = (ls,rxb)" 
shows "res = Some rx' \<Longrightarrow> (\<rightarrow>\<^sub>m)\<^sup>*\<^sup>* (add_mset (t,Var x) (mp_lr mp + M)) (mp_lr (ls,rx') + M) \<and> wf_rx rx'
  \<and> lvars_mp (add_mset (t,Var x) (mp_lr mp + M)) \<supseteq> lvars_mp (mp_lr (ls,rx') + M)"
    "res = None \<Longrightarrow> match_fail (add_mset (t,Var x) (mp_lr mp + M))"     
proof -
  obtain rx b where rxb: "rxb = (rx,b)" by force
  note [simp] = List.maps_def
  note res = res[unfolded insert_rx_def]
  {
    assume *: "res = None" 
    with res rxb obtain ts where look: "map_of rx x = Some ts" by (auto split: option.splits)
    with res[unfolded look Let_def rxb split] * obtain t' where t': "t' \<in> set ts" and clash: "Conflict_Clash t t'" 
      by (auto split: if_splits option.splits)
    from map_of_SomeD[OF look] t' have "(t',Var x) \<in># mp_rx rxb"
        unfolding mp_rx_def rxb by auto
    hence "(t',Var x) \<in># mp_lr mp + M" unfolding mp mp_lr_def by auto
    then obtain mp' where mp: "mp_lr mp + M = add_mset (t',Var x) mp'" by (rule mset_add)    
    show "match_fail (add_mset (t,Var x) (mp_lr mp + M))" unfolding mp  
      by (rule match_clash'[OF clash])
  }
  {
    assume "res = Some rx'" 
    note res = res[unfolded this rxb split]
    show "mp_step_mset^** (add_mset (t,Var x) (mp_lr mp + M)) (mp_lr (ls,rx') + M) \<and> wf_rx rx'
     \<and> lvars_mp (mp_lr (ls, rx') + M) \<subseteq> lvars_mp (add_mset (t, Var x) (mp_lr mp + M))"
    proof (cases "map_of rx x")
      case look: None
      from res[unfolded this] 
      have rx': "rx' = ((x,[t]) # rx, b)" by auto
      have id: "mp_rx rx' = add_mset (t, Var x) (mp_rx rxb)"
        using look unfolding mp_rx_def mset_concat_union mset_map rx' o_def rxb
        by auto
      have [simp]: "(x, t) \<notin> set rx" for t using look 
        using weak_map_of_SomeI by force
      have "inf_var_conflict (mp_mset (mp_rx ((x, [t]) # rx, b))) = inf_var_conflict (mp_mset (mp_rx (rx, b)))" 
        unfolding mp_rx_def fst_conv inf_var_conflict_def
        by (intro ex_cong1, auto)
      hence wf: "wf_rx rx'" using wf look unfolding wf_rx_def rx' rxb by (auto simp: wf_ts_def)
      show ?thesis unfolding mp mp_lr_def split id
        using wf unfolding rx' by auto
    next
      case look: (Some ts)
      from map_of_SomeD[OF look] have mem: "(x,ts) \<in> set rx" by auto
      note res = res[unfolded look option.simps Let_def]
      from res obtain cs where those: "those (map (conflicts t) ts) = Some cs" by (auto split: option.splits)
      note res = res[unfolded those option.simps]
      from arg_cong[OF those[unfolded those_eq_Some], of set] have confl: "conflicts t ` set ts = Some ` set cs" by auto
      show ?thesis
      proof (cases "[] \<in> set cs")
        case True
        with res have rx': "rx' = rxb" by (auto split: if_splits simp: mp rxb those)
        from True confl obtain t' where "t' \<in> set ts" and "conflicts t t' = Some []" by force
        hence t: "t \<in> set ts" using conflicts(5)[of t t'] by auto  
        hence "(t, Var x) \<in># mp_rx rxb" unfolding mp_rx_def rxb using mem by auto
        hence "(t, Var x) \<in># mp_lr mp + M" unfolding mp mp_lr_def by auto
        then obtain sub where id: "mp_lr mp + M = add_mset (t, Var x) sub" by (rule mset_add)
        show ?thesis unfolding id rx' mp[symmetric] using match_duplicate[of "(t, Var x)" sub] wf
          by (auto simp: lvars_mp_def)
      next
        case False
        with res have rx': "rx' = (AList.update x (t # ts) rx, b \<or> (\<exists>y\<in>set (concat cs). inf_sort (snd y)))" by (auto split: if_splits)
        from split_list[OF mem] obtain rx1 rx2 where rx: "rx = rx1 @ (x,ts) # rx2" by auto 
        have id: "mp_rx rx' = add_mset (t, Var x) (mp_rx rxb)" 
          unfolding rx' mp_rx_def rxb by (simp add: mset_update[OF look] mset_concat_union, auto simp: rx)
        from wf[unfolded wf_rx_def] rx rxb have ts: "wf_ts ts" and b: "b = inf_var_conflict (mp_mset (mp_rx rxb))" by auto
        from False confl conflicts(5)[of t t] have t: "t \<notin> set ts" by force
        from confl have "None \<notin> set (map (conflicts t) ts)" by auto
        with ts t have ts': "wf_ts (t # ts)" unfolding wf_ts_def 
          apply clarsimp
          subgoal for j i by (cases j, force, cases i; force simp: set_conv_nth)
          done
        have b: "(b \<or> (\<exists>y\<in>set (concat cs). inf_sort (snd y))) = inf_var_conflict (mp_mset (add_mset (t, Var x) (mp_rx rxb)))" (is "_ = ?ivc")
        proof (standard, elim disjE bexE)
          show "b \<Longrightarrow> ?ivc" unfolding b inf_var_conflict_def by force
          {
            fix y
            assume y: "y \<in> set (concat cs)" and inf: "inf_sort (snd y)" 
            from y confl obtain t' ys where t': "t' \<in> set ts" and c: "conflicts t t' = Some ys" and y: "y \<in> set ys" unfolding set_concat
              by (smt (verit, del_insts) UnionE image_iff)
            have y: "Conflict_Var t t' y" using c y by auto
            from mem t' have "(t',Var x) \<in># mp_rx rxb" unfolding rxb mp_rx_def by auto  
            thus ?ivc unfolding inf_var_conflict_def using inf y by fastforce
          }
          assume ?ivc
          from this[unfolded inf_var_conflict_def]
          obtain s1 s2 x' y
            where ic: "(s1, Var x') \<in># add_mset (t, Var x) (mp_rx rxb) \<and> (s2, Var x') \<in># add_mset (t, Var x) (mp_rx rxb) \<and> Conflict_Var s1 s2 y \<and> inf_sort (snd y)"
            by blast
          show "b \<or> (\<exists>y\<in>set (concat cs). inf_sort (snd y))" 
          proof (cases "(s1, Var x') \<in># mp_rx rxb \<and> (s2, Var x') \<in># mp_rx rxb")
            case True
            with ic have b unfolding b inf_var_conflict_def by blast
            thus ?thesis ..
          next
            case False
            with ic have "(s1,Var x') = (t,Var x) \<or> (s2,Var x') = (t,Var x)" by auto
            hence "\<exists> s y. (s, Var x) \<in># add_mset (t, Var x) (mp_rx rxb) \<and> Conflict_Var t s y \<and> inf_sort (snd y)" 
            proof
              assume "(s1, Var x') = (t, Var x)" 
              thus ?thesis using ic by blast
            next
              assume *: "(s2, Var x') = (t, Var x)" 
              with ic have "Conflict_Var s1 t y" by auto
              hence "Conflict_Var t s1 y" using conflicts_sym[of s1 t] by (cases "conflicts s1 t"; cases "conflicts t s1", auto)
              with ic * show ?thesis by blast
            qed
            then obtain s y where sx: "(s, Var x) \<in># add_mset (t, Var x) (mp_rx rxb)" and y: "Conflict_Var t s y" and inf: "inf_sort (snd y)" 
              by blast
            from wf have dist: "distinct (map fst rx)" unfolding wf_rx_def rxb by auto
            from y have "s \<noteq> t" by auto
            with sx have "(s, Var x) \<in># mp_rx rxb" by auto
            hence "s \<in> set ts" unfolding mp_rx_def rxb using mem eq_key_imp_eq_value[OF dist] by auto
            with y confl have "y \<in> set (concat cs)" by (cases "conflicts t s"; force)
            with inf show ?thesis by auto
          qed
        qed  
        have wf: "wf_rx rx'" using wf ts' unfolding wf_rx_def id unfolding rx' rxb snd_conv b by (auto simp: distinct_update set_update[OF look])
        show ?thesis using wf id unfolding mp by (auto simp: mp_lr_def)
      qed
    qed
  }
qed

lemma decomp_impl: "decomp_impl mp = res \<Longrightarrow> 
    (res = Some mp' \<longrightarrow> (\<rightarrow>\<^sub>m)\<^sup>*\<^sup>* (mp_list mp + M) (mp_lr mp' + M) \<and> wf_lr mp' 
      \<and> lvars_mp (mp_list mp + M) \<supseteq> lvars_mp (mp_lr mp' + M))
  \<and> (res = None \<longrightarrow> (\<exists> mp'. (\<rightarrow>\<^sub>m)\<^sup>*\<^sup>* (mp_list mp + M) mp' \<and> match_fail mp'))" 
proof (induct mp arbitrary: res M mp' rule: decomp_impl.induct)
  case 1
  thus ?case by (auto simp: mp_lr_def mp_rx_def List.maps_def wf_lr_def wf_lx_def wf_rx_def inf_var_conflict_def)
next
  case (2 f ts g ls mp res M mp')
  have id: "mp_list ((Fun f ts, Fun g ls) # mp) + M = add_mset (Fun f ts, Fun g ls) (mp_list mp + M)" 
    by auto
  show ?case 
  proof (cases "(f,length ts) = (g,length ls)")
    case False
    with 2(2-) have res: "res = None" by auto
    from match_clash[OF False, of "(mp_list mp + M)", folded id]
    show ?thesis unfolding res by blast
  next
    case True
    have id2: "mp_list (zip ts ls @ mp) + M = mp_list mp + M + mp_list (zip ts ls)" 
      by auto
    from True 2(2-) have res: "decomp_impl (zip ts ls @ mp) = res" by auto
    note IH = 2(1)[OF True this, of mp' M]
    note step = match_decompose[OF True, of "mp_list mp + M", folded id id2]
    have lvars: "lvars_mp (mp_list ((Fun f ts, Fun g ls) # mp) + M) \<supseteq> lvars_mp (mp_list (zip ts ls @ mp) + M)" 
      by (auto simp: lvars_mp_def dest: set_zip_rightD)
    from IH step subset_trans[OF _ lvars] 
    show ?thesis by (meson converse_rtranclp_into_rtranclp)
  qed
next
  case (3 x g ls mp res M mp')
  note res = 3(2)[unfolded decomp_impl.simps]
  show ?case
  proof (cases "decomp_impl mp")
    case None
    from 3(1)[OF None, of mp' "add_mset (Var x, Fun g ls) M"] None res show ?thesis by auto
  next
    case (Some mpx)
    then obtain lx rx where decomp: "decomp_impl mp = Some (lx,rx)" by (cases mpx, auto)
    from res[unfolded decomp option.simps split] have res: "res = Some ( (x, Fun g ls) # lx, rx)" by auto
    from 3(1)[OF decomp, of "(lx, rx)" "add_mset (Var x, Fun g ls) M"] res
    show ?thesis by (auto simp: mp_lr_def wf_lr_def wf_lx_def)
  qed
next
  case (4 t y mp res M mp')
  note res = 4(2)[unfolded decomp_impl.simps]
  show ?case
  proof (cases "decomp_impl mp")
    case None
    from 4(1)[OF None, of mp' "add_mset (t, Var y) M"] None res show ?thesis by auto
  next
    case (Some mpx)
    then obtain lx rx where decomp: "decomp_impl mp = Some (lx,rx)" by (cases mpx, auto)
    note res = res[unfolded decomp option.simps split]
    from 4(1)[OF decomp, of "( lx, rx)" "add_mset (t, Var y) M"]
    have IH: "(\<rightarrow>\<^sub>m)\<^sup>*\<^sup>* (mp_list ((t, Var y) # mp) + M) (mp_lr ( lx, rx) + add_mset (t, Var y) M)"
      "wf_lr ( lx, rx)" 
      "lvars_mp (mp_lr (lx, rx) + add_mset (t, Var y) M)
       \<subseteq> lvars_mp (mp_list mp + add_mset (t, Var y) M)" by auto
    from IH have wf_rx: "wf_rx rx" unfolding wf_lr_def by auto
    show ?thesis 
    proof (cases "insert_rx t y rx")
      case None
      with res have res: "res = None" by auto
      from insert_rx(2)[OF None wf_rx refl refl, of lx M]
        IH res show ?thesis by auto
    next
      case (Some rx')
      with res have res: "res = Some ( lx, rx')" by auto
      from insert_rx(1)[OF Some wf_rx refl refl, of lx M]
      have wf_rx: "wf_rx rx'" 
        and steps: "(\<rightarrow>\<^sub>m)\<^sup>*\<^sup>* (mp_lr ( lx, rx) + add_mset (t, Var y) M) (mp_lr ( lx, rx') + M)" 
        and lvars: "lvars_mp (mp_lr (lx, rx') + M) \<subseteq> lvars_mp (add_mset (t, Var y) (mp_lr (lx, rx) + M))" 
        by auto
      from IH(1) steps
      have steps: "(\<rightarrow>\<^sub>m)\<^sup>*\<^sup>* (mp_list ((t, Var y) # mp) + M) (mp_lr ( lx, rx') + M)" by auto
      from wf_rx IH(2-) have wf: "wf_lr ( lx, rx')"  
        unfolding wf_lr_def by auto
      from res wf steps lvars IH(3) show ?thesis by auto
    qed
  qed
qed

lemma match_decomp_lin_impl: "match_decomp_lin_impl mp = res \<Longrightarrow> ll_mp (mp_list mp + M) \<Longrightarrow>
    (res = Some mp' \<longrightarrow> (\<rightarrow>\<^sub>m)\<^sup>*\<^sup>* (mp_list mp + M) (mp_list (mp_lx mp') + M) \<and> wf_lx mp' \<and> ll_mp (mp_list (mp_lx mp') + M))
  \<and> (res = None \<longrightarrow> (\<exists> mp'. (\<rightarrow>\<^sub>m)\<^sup>*\<^sup>* (mp_list mp + M) mp' \<and> match_fail mp'))" 
proof (induct mp arbitrary: res M mp' rule: match_decomp_lin_impl.induct)
  case 1
  thus ?case by (auto simp: mp_lr_def wf_lx_def)
next
  case (2 f ts g ls mp res M mp')
  have id: "mp_list ((Fun f ts, Fun g ls) # mp) + M = add_mset (Fun f ts, Fun g ls) (mp_list mp + M)" 
    by auto
  show ?case 
  proof (cases "(f,length ts) = (g,length ls)")
    case False
    with 2(2-) have res: "res = None" by auto
    from match_clash[OF False, of "(mp_list mp + M)", folded id]
    show ?thesis unfolding res by blast
  next
    case True
    have id2: "mp_list (zip ts ls @ mp) + M = mp_list mp + M + mp_list (zip ts ls)" 
      by auto
    from True 2(2-) have res: "match_decomp_lin_impl (zip ts ls @ mp) = res" by auto
    have imag_snd: "image_mset snd (mp_list (zip ts ls)) = mset ls" using True 
      by simp (metis map_snd_zip mset_map)
    have "vars_mp_mset (mp_list ((Fun f ts, Fun g ls) # mp) + M)
      = vars_term_ms (Fun g ls) + vars_mp_mset (mp_list mp + M)" 
      unfolding vars_mp_mset_def by auto
    also have "vars_term_ms (Fun g ls) = vars_mp_mset (mp_list (zip ts ls))" 
      unfolding vars_mp_mset_def image_mset.comp[symmetric]
      unfolding o_def imag_snd by simp
    finally have "vars_mp_mset (mp_list ((Fun f ts, Fun g ls) # mp) + M)
         = vars_mp_mset (mp_list (zip ts ls @ mp) + M)" 
      unfolding vars_mp_mset_def by auto
    with 2(3) have ll: "ll_mp (mp_list (zip ts ls @ mp) + M)" unfolding ll_mp_def by auto
    note IH = 2(1)[OF True res ll, of mp' ]
    note step = match_decompose[OF True, of "mp_list mp + M", folded id id2]
    from IH step subset_trans 
    show ?thesis by (meson converse_rtranclp_into_rtranclp)
  qed
next
  case (3 x g ls mp res M mp')
  note res = 3(2)[unfolded match_decomp_lin_impl.simps]
  from 3(3) have ll: "ll_mp (mp_list mp + add_mset (Var x, Fun g ls) M)" by simp
  note IH = 3(1)[OF _ ll]
  show ?case
  proof (cases "match_decomp_lin_impl mp")
    case None
    from IH[OF None] None res show ?thesis by auto
  next
    case (Some mpx)
    then obtain lx where decomp: "match_decomp_lin_impl mp = Some lx" by (cases mpx, auto)
    from res[unfolded decomp option.simps split] have res: "res = Some ( (x, Fun g ls) # lx)" by auto
    from IH[OF decomp, of lx] res
    show ?thesis by (auto simp: wf_lx_def)
  qed
next
  case (4 t y mp res M mp')
  note res = 4(2)[unfolded match_decomp_lin_impl.simps]
  have "vars_mp_mset (mp_list mp + M) \<subseteq># vars_mp_mset (mp_list ((t, Var y) # mp) + M)" 
    unfolding vars_mp_mset_def by auto
  with 4(3) have ll_new: "ll_mp (mp_list mp + M)" unfolding ll_mp_def
    by (meson dual_order.trans subseteq_mset_def)
  have "mp_list ((t, Var y) # mp) + M = add_mset (t, Var y) (mp_list mp + M)" by auto
  also have "\<dots> \<rightarrow>\<^sub>m mp_list mp + M" 
  proof (rule match_match)
    from 4(3)[unfolded ll_mp_def]
    have "count (vars_mp_mset (mp_list ((t, Var y) # mp) + M)) y \<le> 1" by auto
    hence "count (vars_mp_mset (mp_list mp + M)) y = 0" 
      unfolding vars_mp_mset_def by auto
    hence "y \<notin># vars_mp_mset (mp_list mp + M)"
      by (simp add: not_in_iff)
    hence "y \<notin> set_mset (vars_mp_mset (mp_list mp + M))" by blast
    also have "set_mset (vars_mp_mset (mp_list mp + M)) = \<Union> (vars ` snd ` mp_mset (mp_list mp + M))" 
      unfolding vars_mp_mset_def o_def by auto
    finally show "y \<notin> \<Union> (vars ` snd ` mp_mset (mp_list mp + M))" by auto
  qed
  finally have "mp_list ((t, Var y) # mp) + M \<rightarrow>\<^sub>m mp_list mp + M" .
  note step = converse_rtranclp_into_rtranclp[of mp_step_mset, OF this]
  note IH = 4(1)[OF _ ll_new]
  show ?case
  proof (cases "match_decomp_lin_impl mp")
    case None
    with IH[OF None] res step show ?thesis by fastforce
  next
    case (Some mpx)
    with IH[OF Some, of mpx] res step show ?thesis by fastforce
  qed
qed


lemma pat_inner_lin_impl: assumes "pat_inner_lin_impl p pd = res" 
  and "wf_pat_lx pd" "\<forall> mp \<in> set p. ll_mp (mp_list mp)" 
  and "tvars_pat (pat_mset (pat_mset_list p + pat_lx pd)) \<subseteq> V" 
  shows "res = None \<Longrightarrow> (add_mset (pat_mset_list p + pat_lx pd) P, P) \<in> \<Rrightarrow>\<^sup>+" 
    and "res = Some p' \<Longrightarrow> (add_mset (pat_mset_list p + pat_lx pd) P, add_mset (pat_lx p') P) \<in> \<Rrightarrow>\<^sup>*
             \<and> wf_pat_lx p' \<and> tvars_pat (pat_mset (pat_lx p')) \<subseteq> V" 
proof (atomize(full), insert assms, induct p arbitrary: pd res p')
  case Nil
  then show ?case by (auto simp: wf_pat_lr_def pat_mset_list_def pat_lr_def)
next
  case (Cons mp p pd res p')
  let ?p = "pat_mset_list p + pat_lx pd" 
  have id: "pat_mset_list (mp # p) + pat_lx pd = add_mset (mp_list mp) ?p" unfolding pat_mset_list_def by auto  
  from Cons(4) have "ll_mp (mp_list mp + {#})" by auto
  note match = match_decomp_lin_impl[OF _ this]
  note res = Cons(2)[unfolded pat_inner_lin_impl.simps]
  from Cons(4) have llp: "\<forall>mp\<in>set p. ll_mp (mp_list mp)" 
    and ll_mp: "ll_mp (mp_list mp)" by auto
  show ?case
  proof (cases "match_decomp_lin_impl mp")
    case (Some mp')
    from match[OF this, of mp']
    have steps: "(\<rightarrow>\<^sub>m)\<^sup>*\<^sup>* (mp_list mp) (mp_list (mp_lx mp'))" and wf: "wf_lx mp'" 
      and ll_mp': "ll_mp (mp_list (mp_lx mp'))" by auto
    from mp_step_mset_steps_vars[OF steps]
    have tvars: "tvars_match (mp_mset (mp_list (mp_lx mp'))) \<subseteq> tvars_match (mp_mset (mp_list mp))" by auto
    note Psteps = mp_step_mset_cong[OF steps, of ?p P, folded id]
    note res = res[unfolded Some option.simps]
    show ?thesis
    proof (cases "mp' = []")
      case True
      with res have res: "res = None" by auto
      from True have empty: "mp_list (mp_lx mp') = {#}" by auto
      have "(add_mset (add_mset (mp_list (mp_lx mp')) ?p) P, {#} + P) \<in> \<Rrightarrow>"
        unfolding empty unfolding P_step_def 
        by (standard, unfold split, rule P_simp_pp, rule pat_remove_pp)
      with Psteps  
      show ?thesis using res by auto
    next
      case False
      with res have res: "pat_inner_lin_impl p (mp' # pd) = res" by auto
      have "wf_pat_lx (mp' # pd)" using wf ll_mp' Cons(3) False 
        unfolding wf_pat_lx_def by auto
      note IH = Cons(1)[OF res this llp, of p']
      have tvars: "tvars_pat (pat_mset (pat_mset_list p + pat_lx (mp' # pd))) \<subseteq> V" 
        using tvars Cons(5) unfolding tvars_pat_def 
        by (auto simp: pat_lx_def pat_mset_list_def)
      note IH = IH[OF this]
      define I1 where "I1 = add_mset (pat_mset_list p + pat_lx (mp' # pd)) P" 
      define I2 where "I2 = add_mset (add_mset (mp_list (mp_lx mp')) (pat_mset_list p + pat_lx pd)) P" 
      have "I2 = I1" unfolding I1_def I2_def by (auto simp: pat_lx_def)
      define S where "S = add_mset (pat_mset_list (mp # p) + pat_lx pd) P" 
      define E where "E = add_mset (pat_lx p') P" 
      from IH Psteps show ?thesis 
        unfolding I1_def[symmetric] I2_def[symmetric] S_def[symmetric] E_def[symmetric]
        unfolding \<open>I2 = I1\<close> by auto
    qed
  next
    case None
    from match[OF None] obtain mp' where
      msteps: "(\<rightarrow>\<^sub>m)\<^sup>*\<^sup>* (mp_list mp) mp'" and fail: "match_fail mp'" by auto
    note steps = mp_step_mset_cong[OF this(1), of ?p P, folded id]
    note tvars = mp_step_mset_steps_vars[OF msteps]
    from P_simp_pp[OF pat_remove_mp[OF fail, of ?p], of P]
    have "(add_mset (add_mset mp' ?p) P, add_mset ?p P) \<in> P_step" 
      unfolding P_step_def by auto
    with steps have steps: "(add_mset (pat_mset_list (mp # p) + pat_lx pd) P, add_mset ?p P) \<in> P_step^*" by auto
    from res[unfolded None option.simps]
    have res: "pat_inner_lin_impl p pd = res" by auto
    note IH = Cons(1)[OF res Cons(3) llp, of p']
    have "tvars_pat (pat_mset (pat_mset_list p + pat_lx pd)) \<subseteq> V" 
      using Cons(5) unfolding tvars_pat_def 
      by (auto simp: pat_lx_def pat_mset_list_def)
    from IH[OF this] steps tvars
    show ?thesis by auto
  qed
qed

lemma pat_mset_list: "pat_mset (pat_mset_list p) = pat_list p" 
  unfolding pat_list_def pat_mset_list_def by (auto simp: image_comp)

lemma vars_mp_mset_subst: "vars_mp_mset (mp_list (subst_match_problem_list \<tau> mp)) 
  = vars_mp_mset (mp_list mp)" 
  unfolding vars_mp_mset_def subst_match_problem_list_def subst_left_def
  by (simp add: image_mset.comp[symmetric], intro
    arg_cong[of _ _ "\<lambda> xs. \<Sum>\<^sub># (image_mset vars_term_ms xs)"])
    (induct mp, auto)

lemma subst_conversion: "map (\<lambda>\<tau>. subst_pat_problem_mset \<tau> (pat_mset_list p)) xs =
    map pat_mset_list (map (\<lambda>\<tau>. subst_pat_problem_list \<tau> p) xs)" 
  unfolding subst_pat_problem_list_def subst_pat_problem_mset_def subst_match_problem_mset_def
    subst_match_problem_list_def map_map o_def
  by (intro list.map_cong0, auto simp: pat_mset_list_def o_def image_mset.compositionality)
  

lemma ll_mp_subst: "ll_mp (mp_list (subst_match_problem_list \<tau> mp)) = ll_mp (mp_list mp)" 
  unfolding ll_mp_def vars_mp_mset_subst by simp


lemma ll_pp_subst: "ll_pp (subst_pat_problem_list \<tau> p) = ll_pp p" 
  unfolding ll_pp_def subst_pat_problem_list_def using ll_mp_subst[of \<tau>]
  by auto


text \<open>Main simulation lemma for a single @{const pat_lin_impl} step.\<close>
lemma pat_lin_impl:
  assumes "pat_lin_impl n p = res" 
    and vars: "tvars_pat (pat_list p) \<subseteq> {..<n} \<times> S"
    and linear: "ll_pp p"  
  shows "res = None \<Longrightarrow> \<exists> p'. (add_mset (pat_mset_list p) P, add_mset p' P) \<in> \<Rrightarrow>\<^sup>* \<and> pat_fail p'" 
    and "res = Some ps \<Longrightarrow> (add_mset (pat_mset_list p) P, mset (map pat_mset_list ps) + P) \<in> \<Rrightarrow>\<^sup>+
             \<and> tvars_pat (\<Union> (pat_list ` set ps)) \<subseteq> {..< n + m} \<times> S
             \<and> Ball (set ps) ll_pp" 
proof (atomize(full), goal_cases)
  case 1
  have wf: "wf_pat_lx []" unfolding wf_pat_lx_def by auto
  have vars: "tvars_pat (pat_mset (pat_mset_list p)) \<subseteq> {..<n} \<times> S"
    using vars unfolding pat_mset_list by auto
  have "pat_mset_list p + pat_lx [] = pat_mset_list p" unfolding pat_lx_def by auto
  note pat_inner = pat_inner_lin_impl[OF refl wf, of p, unfolded this, OF linear[unfolded ll_pp_def] vars]
  note res = assms(1)[unfolded pat_lin_impl_def]
  show ?case
  proof (cases "pat_inner_lin_impl p []")
    case None
    from pat_inner(1)[OF this] res[unfolded None option.simps] vars
    show ?thesis by (auto simp: tvars_pat_def)
  next
    case (Some p')
    from pat_inner(2)[OF Some]
    have steps: "(add_mset (pat_mset_list p) P, add_mset (pat_lx p') P) \<in> \<Rrightarrow>\<^sup>*"
      and wf: "wf_pat_lx p'"
      and varsp': "tvars_pat (pat_mset (pat_lx p')) \<subseteq> {..<n} \<times> S"
      by auto
    note res = res[unfolded Some option.simps]
    show ?thesis
    proof (cases p')
      case Nil
      with res have res: "res = None" by auto
      from Nil have "pat_lx p' = {#}" by (auto simp: pat_lx_def)
      hence fail: "pat_fail (pat_lx p')"
        using pat_empty by auto
      from fail res steps show ?thesis by auto
    next
      case (Cons mp mps)
      from wf[unfolded Cons wf_pat_lx_def] have mp: "wf_lx mp" "mp \<noteq> []" by auto
      then obtain f ts x mp' where "mp = (x,Fun f ts) # mp'" 
        by (cases mp; cases "snd (hd mp)", auto simp: wf_lx_def)
      note Cons = Cons[unfolded this]
      from Cons have id: "(p' = []) = False" by auto
      define p'l where "p'l = map mp_lx p'" 
      note res = res[unfolded Cons list.sel fst_conv, folded Cons, unfolded id if_False Let_def]
      from res have res: "res = Some (map (\<lambda>\<tau>. subst_pat_problem_list \<tau> p'l) (\<tau>s_list n x))" 
        by (auto simp: p'l_def)
      show ?thesis
      proof (intro conjI impI)
        assume "res = Some ps" 
        with res have ps_def: "ps = map (\<lambda>\<tau>. subst_pat_problem_list \<tau> p'l) (\<tau>s_list n x)" by auto
        have id: "pat_lx p' = pat_mset_list p'l" unfolding p'l_def pat_lx_def pat_mset_list_def
          by auto
        have ll: "ll_pp p'l" unfolding p'l_def using wf unfolding wf_pat_lx_def ll_pp_def by auto
        thus "Ball (set ps) ll_pp" unfolding ps_def using ll_pp_subst by auto 
        have subst: "map (\<lambda>\<tau>. subst_pat_problem_mset \<tau> (pat_lx p')) (\<tau>s_list n x) = map pat_mset_list ps"
          unfolding id
          unfolding ps_def subst_pat_problem_list_def subst_pat_problem_mset_def subst_match_problem_mset_def
            subst_match_problem_list_def map_map o_def
          by (intro list.map_cong0, auto simp: pat_mset_list_def o_def image_mset.compositionality)
        have step: "(add_mset (pat_lx p') P, mset (map pat_mset_list ps) + P) \<in> \<Rrightarrow>"
          unfolding P_step_def 
        proof (standard, unfold split, intro P_simp_pp)
          note x = Some[unfolded find_var_def]
          have disj: "tvars_disj_pp {n..<n + m} (pat_mset (pat_lx p'))" 
            using varsp' unfolding tvars_pat_def tvars_disj_pp_def tvars_match_def by force
          obtain mp'' p'' where expand: "pat_lx p' = add_mset (add_mset (Var x, Fun f ts) mp'') p''" 
            unfolding Cons pat_lx_def by auto
          have "pat_lx p' \<Rightarrow>\<^sub>m mset (map (\<lambda>\<tau>. subst_pat_problem_mset \<tau> (pat_lx p')) (\<tau>s_list n x))" (is "_ \<Rightarrow>\<^sub>m ?ps")
            using pat_instantiate[OF disj[unfolded expand], folded expand, of x "Fun f ts"]
            by auto
          also have "?ps = mset (map pat_mset_list ps)" 
            unfolding ps_def id unfolding subst_conversion ..
          finally show "pat_lx p' \<Rightarrow>\<^sub>m mset (map pat_mset_list ps)" by auto
        qed
        with steps
        show "(add_mset (pat_mset_list p) P, mset (map pat_mset_list ps) + P) \<in> \<Rrightarrow>\<^sup>+" 
          by auto
        show "tvars_pat (\<Union> (pat_list ` set ps)) \<subseteq> {..<n + m} \<times> S"
        proof (safe del: conjI)
          fix yn \<iota>
          assume "(yn,\<iota>) \<in> tvars_pat (\<Union> (pat_list ` set ps))" 
          then obtain pi mp
            where pi: "pi \<in> set ps"
              and mp: "mp \<in> set pi" and y: "(yn,\<iota>) \<in> tvars_match (set mp)"
            unfolding tvars_pat_def pat_list_def by force
          from pi[unfolded ps_def set_map subst_pat_problem_list_def subst_match_problem_list_def, simplified] 
          obtain \<tau> where tau: "\<tau> \<in> set (\<tau>s_list n x)" and pi: "pi = map (map (subst_left \<tau>)) p'l" by auto
          from tau[unfolded \<tau>s_list_def]
          obtain info where infoCl: "info \<in> set (Cl (snd x))" and tau: "\<tau> = \<tau>c n x info" by auto
          from Cl_len[of "snd x"] this(1) have len: "length (snd info) \<le> m" by force
          from mp[unfolded pi set_map] obtain mp' where mp': "mp' \<in> set p'l" and mp: "mp = map (subst_left \<tau>) mp'" by auto
          from y[unfolded mp tvars_match_def image_comp o_def set_map]
          obtain pair where *: "pair \<in> set mp'" "(yn,\<iota>) \<in> vars (fst (subst_left \<tau> pair))" by auto
          obtain s t where pair: "pair = (s,t)" by force
          from *[unfolded pair] have st: "(s,t) \<in> set mp'" and y: "(yn,\<iota>) \<in> vars (s \<cdot> \<tau>)" unfolding subst_left_def by auto
          from y[unfolded vars_term_subst, simplified]
          obtain z where z: "z \<in> vars s" and y: "(yn,\<iota>) \<in> vars (\<tau> z)" by auto
          obtain f ss where info: "info = (f,ss)" by (cases info, auto)
          with len have len: "length ss \<le> m" by auto
          define ts :: "('f,_)term list" where "ts = map Var (zip [n..<n + length ss] ss)" 
          from tau[unfolded \<tau>c_def info split]
          have tau: "\<tau> = subst x (Fun f ts)" unfolding ts_def by auto
          from infoCl[unfolded Cl info]
          have f: "f : ss \<rightarrow> snd x in C" by auto
          from C_sub_S[OF this] have ssS: "set ss \<subseteq> S" by simp
          from ssS
          have "vars (Fun f ts) \<subseteq> {..< n + length ss} \<times> S" unfolding ts_def by (auto simp: set_zip)
          also have "\<dots> \<subseteq> {..< n + m} \<times> S" using len by auto
          finally have subst: "vars (Fun f ts) \<subseteq> {..< n + m} \<times> S" by auto
          show "yn \<in> {..<n + m} \<and> \<iota> \<in> S"
          proof (cases "z = x")
            case True
            with y subst tau show ?thesis by force
          next
            case False
            hence "\<tau> z = Var z" unfolding tau by (auto simp: subst_def)
            with y have "z = (yn,\<iota>)" by auto
            with z have y: "(yn,\<iota>) \<in> vars s" by auto
            with st have "(yn,\<iota>) \<in> tvars_match (set mp')" unfolding tvars_match_def by force
            with mp' have "(yn,\<iota>) \<in> tvars_pat (set ` set p'l)" unfolding tvars_pat_def by auto
            also have "\<dots> = tvars_pat (pat_mset (pat_mset_list p'l))" 
              by (rule arg_cong[of _ _ tvars_pat], auto simp: pat_mset_list_def image_comp)
            also have "\<dots> = tvars_pat (pat_mset (pat_lx p'))" unfolding id[symmetric] by simp
            also have "\<dots> \<subseteq> {..<n} \<times> S" using varsp' .
            finally show ?thesis by auto
          qed
        qed
      qed (insert res, auto)
    qed
  qed
qed

lemma pats_mset_list: "pats_mset (pats_mset_list ps) = pat_list ` set ps" 
  unfolding pat_list_def pat_mset_list_def o_def set_mset_mset set_map
      mset_map image_comp set_image_mset by simp


lemma pats_lin_impl: assumes "\<forall>p \<in> set ps. tvars_pat (pat_list p) \<subseteq> {..<n} \<times> S" 
  and "Ball (set ps) ll_pp" 
  and "\<forall>pp \<in> pat_list ` set ps. wf_pat pp"
  shows "pats_lin_impl n ps = pats_complete C (pat_list ` set ps)" 
proof (insert assms, induct ps arbitrary: n rule: 
    SN_induct[OF SN_inv_image[OF SN_imp_SN_trancl[OF SN_P_step]], of pats_mset_list])
  case (1 ps n)
  note IH = 1(1)  
  note ll = 1(3)
  note wf = 1(4)
  note simps = pats_lin_impl.simps[of n ps]
  show ?case 
  proof (cases ps)
    case Nil
    show ?thesis unfolding simps unfolding Nil by auto
  next
    case (Cons p ps1)
    hence id: "pats_mset_list ps = add_mset (pat_mset_list p) (pats_mset_list ps1)" by auto
    note res = simps[unfolded Cons list.simps, folded Cons]
    from 1(2)[rule_format, of p] Cons have "tvars_pat (pat_list p) \<subseteq> {..<n} \<times> S" by auto
    note pat_impl = pat_lin_impl[OF refl this]
    from ll Cons have "ll_pp p" by auto
    note pat_impl = pat_impl[OF this, where P = "(pats_mset_list ps1)", folded id]
    let ?step = "(\<Rrightarrow>) :: (('f,'v,'s)pats_problem_mset \<times> ('f,'v,'s)pats_problem_mset)set" 
    from wf have "wf_pats (pat_list ` set ps)" unfolding wf_pats_def by auto
    note steps_to_equiv = P_steps_pcorrect[OF this[folded pats_mset_list]]
    show ?thesis
    proof (cases "pat_lin_impl n p")
      case None
      with res have res: "pats_lin_impl n ps = False" by auto
      from pat_impl(1)[OF None]
      obtain p' where steps: "(pats_mset_list ps, add_mset p' (pats_mset_list ps1)) \<in> \<Rrightarrow>\<^sup>*" and fail: "pat_fail p'" 
        by auto
      show ?thesis
      proof (cases "add_mset p' (pats_mset_list ps1) = bottom_mset")
        case True
        with res P_steps_pcorrect[OF _ steps, unfolded pats_mset_list] wf 
        show ?thesis by (auto simp: wf_pats_def)
      next
        case False
        from P_failure[OF fail False] 
        have "(add_mset p' (pats_mset_list ps1), bottom_mset) \<in> \<Rrightarrow>" unfolding P_step_def by auto
        with steps have "(pats_mset_list ps, bottom_mset) \<in> \<Rrightarrow>\<^sup>*" by auto
        from steps_to_equiv[OF this] res show ?thesis unfolding pats_mset_list by simp
      qed
    next
      case (Some ps2)
      with res have res: "pats_lin_impl n ps = pats_lin_impl (n + m) (ps2 @ ps1)" by auto
      from pat_impl(2)[OF Some]
      have steps: "(pats_mset_list ps, mset (map pat_mset_list (ps2 @ ps1))) \<in> \<Rrightarrow>\<^sup>+" 
          and vars: "tvars_pat (\<Union> (pat_list ` set ps2)) \<subseteq> {..<n + m} \<times> S"
          and ll: "Ball (set ps2) ll_pp" 
          by auto
      have vars: "\<forall>p\<in>set (ps2 @ ps1). tvars_pat (pat_list p) \<subseteq> {..<n + m} \<times> S"
      proof
        fix p
        assume "p \<in> set (ps2 @ ps1)" 
        hence "p \<in> set ps2 \<or> p \<in> set ps1" by auto
        thus "tvars_pat (pat_list p) \<subseteq> {..<n+ m} \<times> S" 
        proof
          assume "p \<in> set ps2" 
          hence "tvars_pat (pat_list p) \<subseteq> tvars_pat (\<Union> (pat_list ` set ps2))" 
            unfolding tvars_pat_def by auto
          with vars show ?thesis by auto
        next
          assume "p \<in> set ps1" 
          hence "p \<in> set ps" unfolding Cons by auto
          from 1(2)[rule_format, OF this] show ?thesis by auto
        qed
      qed
      note steps_equiv = steps_to_equiv[OF trancl_into_rtrancl[OF steps]]
      from steps_equiv have "wf_pats (pats_mset (mset (map pat_mset_list (ps2 @ ps1))))" by auto
      hence wf2: "Ball (pat_list ` set (ps2 @ ps1)) wf_pat" unfolding wf_pats_def pats_mset_list[symmetric]
        by auto
      have "pats_lin_impl n ps = pats_lin_impl (n + m) (ps2 @ ps1)" unfolding res by simp
      also have "\<dots> = pats_complete C (pat_list ` set (ps2 @ ps1))"
      proof (rule IH[OF _ vars _ wf2])
        show "(ps, ps2 @ ps1) \<in> inv_image (\<Rrightarrow>\<^sup>+) pats_mset_list" 
          using steps by auto
        show "\<forall>p\<in>set (ps2 @ ps1). ll_pp p" using ll 1(3) Cons by auto
      qed
      also have "\<dots> = pats_complete C (pat_list ` set ps)" using steps_equiv 
        unfolding pats_mset_list[symmetric] by auto
      finally show ?thesis .
    qed
  qed
qed

corollary pat_complete_lin_impl: 
  assumes wf: "snd ` \<Union> (vars ` fst ` set (concat (concat P))) \<subseteq> S" 
  and left_linear: "Ball (set P) ll_pp" 
  shows "pat_complete_lin_impl (P :: ('f,'v,'s)pats_problem_list) \<longleftrightarrow> pats_complete C (pat_list ` set P)" 
proof - 
  have wf: "Ball (pat_list ` set P) wf_pat" 
    unfolding pat_list_def wf_pat_def wf_match_def tvars_match_def using wf[unfolded set_concat image_comp] by force
  let ?l = "(List.maps (map fst o vars_term_list o fst) (concat (concat P)))" 
  define n where "n = Suc (max_list ?l)" 
  have n: "\<forall>p\<in>set P. tvars_pat (pat_list p) \<subseteq> {..<n} \<times> S" 
  proof (safe)
    fix p x \<iota>
    assume p: "p \<in> set P" and xp: "(x,\<iota>) \<in> tvars_pat (pat_list p)" 
    hence "x \<in> set ?l" unfolding List.maps_def tvars_pat_def tvars_match_def pat_list_def 
      by force
    from max_list[OF this] have "x < n" unfolding n_def by auto
    thus "x < n" by auto
    from xp p wf
    show "\<iota> \<in> S" by (auto simp: wf_pat_iff)
  qed  
  have "pat_complete_lin_impl P = pats_lin_impl n P" 
    unfolding pat_complete_lin_impl_def Let_def n_def by auto
  from pats_lin_impl[OF n left_linear wf, folded this]
  show ?thesis by auto
qed


lemma match_var_impl: assumes wf: "wf_lr mp" 
  and "match_var_impl mp = (xs,mpFin)" 
shows "(\<rightarrow>\<^sub>m)\<^sup>*\<^sup>* (mp_lr mp) (mp_lr mpFin)" 
  and "wf_lr2 mpFin" 
  and "lvars_mp (mp_lr mp) \<supseteq> lvars_mp (mp_lr mpFin)" 
  and "set xs = lvars_mp (mp_list (mp_lx (fst mpFin)))" 
proof -
  note [simp] = List.maps_def
  let ?mp' = "snd (match_var_impl mp)" 
  have mpFin: "mpFin = ?mp'" using assms(2) by auto
  from assms obtain xl rx b where mp3: "mp = (xl,(rx,b))" by (cases mp, auto)
  from assms(2) have xs_def: "xs = remdups (List.maps (vars_term_list o snd) xl)" 
    unfolding match_var_impl_def mp3 split Let_def by auto
  have xs: "xl = [] \<Longrightarrow> xs = []" unfolding xs_def by auto
  define f where "f = (\<lambda> (x,ts :: ('f, nat \<times> 's)term list). tl ts \<noteq> [] \<or> x \<in> set xs)" 
  define mp' where "mp' = mp_rx (filter f rx, b) + mp_list (mp_lx xl)" 
  define deleted where "deleted = mp_rx (filter (Not o f) rx, b)" 
  have mp': "mp_lr ?mp' = mp'" "?mp' = (xl, (filter f rx,b))" 
    unfolding mp3 mp'_def match_var_impl_def split xs_def f_def mp_lr_def by auto
  have "mp_rx (rx,b) = mp_rx (filter f rx, b) + mp_rx (filter (Not o f) rx, b)" 
    unfolding mp_rx_def List.maps_def by (induct rx, auto)
  hence mp: "mp_lr mp = deleted + mp'" unfolding mp3 mp_lr_def mp'_def deleted_def by auto
  have "inf_var_conflict (mp_mset (mp_rx (filter f rx, b))) = inf_var_conflict (mp_mset (mp_rx (rx, b)))" (is "?ivcf = ?ivc")
  proof
    show "?ivcf \<Longrightarrow> ?ivc" unfolding inf_var_conflict_def mp_rx_def fst_conv List.maps_def by force
    assume ?ivc 
    from this[unfolded inf_var_conflict_def]
    obtain s t x y where s: "(s, Var x) \<in># mp_rx (rx, b)" and t: "(t, Var x) \<in># mp_rx (rx, b)" and c: "Conflict_Var s t y" and inf: "inf_sort (snd y)" 
      by blast
    from c conflicts(5)[of s t] have st: "s \<noteq> t" by auto
    from s[unfolded mp_rx_def List.maps_def]
    obtain ss where xss: "(x,ss) \<in> set rx" and s: "s \<in> set ss" by auto
    from t[unfolded mp_rx_def List.maps_def]
    obtain ts where xts: "(x,ts) \<in> set rx" and t: "t \<in> set ts" by auto
    from wf[unfolded mp3 wf_lr_def wf_rx_def] have "distinct (map fst rx)" by auto
    from eq_key_imp_eq_value[OF this xss xts] t have t: "t \<in> set ss" by auto
    with s st have "f (x,ss)" unfolding f_def by (cases ss; cases "tl ss"; auto)
    hence "(x, ss) \<in> set (filter f rx)" using xss by auto
    with s t have "(s, Var x) \<in># mp_rx (filter f rx, b)" "(t, Var x) \<in># mp_rx (filter f rx, b)"
      unfolding mp_rx_def List.maps_def by auto
    with c inf 
    show ?ivcf unfolding inf_var_conflict_def by blast
  qed        
  also have "\<dots> = b" using wf unfolding mp3 wf_lr_def wf_rx_def by auto
  finally have ivcf: "?ivcf = b" .
  have "wf_lr2 ?mp'" 
  proof (cases "xl = []")
    case False
    from ivcf False wf[unfolded mp3] show ?thesis
      unfolding mp' wf_lr2_def wf_lr_def split wf_rx_def by (auto simp: distinct_map_filter)
  next
    case True
    with xs have "xs = []" by auto
    with True wf[unfolded mp3]
    show ?thesis
      unfolding wf_lr2_def mp' split wf_rx2_def wf_rx_def ivcf
      unfolding mp' wf_lr2_def wf_lr_def split wf_rx_def wf_rx2_def wf_ts_def wf_ts2_def f_def 
      apply (clarsimp simp: distinct_map_filter)
      subgoal for x ts by (cases ts; cases "tl ts"; force)
      done
  qed
  thus "wf_lr2 mpFin" unfolding mpFin .
  {
    fix xt t
    assume del: "(t, xt) \<in># deleted" 
    from this[unfolded deleted_def mp_rx_def, simplified]
    obtain x ts where mem: "(x,ts) \<in> set rx" and nf: "\<not> f (x, ts)" and t: "t \<in> set ts" and xt: "xt = Var x" by force
    note del = del[unfolded xt]
    from nf[unfolded f_def split] t have xxs: "x \<notin> set xs" and ts: "ts = [t]" by (cases ts; cases "tl ts", auto)+
    from split_list[OF mem[unfolded ts]] obtain rx1 rx2 where rx: "rx = rx1 @ (x,[t]) # rx2" by auto
    from wf[unfolded wf_lr_def mp3] have wf: "wf_rx (rx,b)" by auto
    hence "distinct (map fst rx)" unfolding wf_rx_def by auto  
    with rx have xrx: "x \<notin> fst ` set rx1 \<union> fst ` set rx2" by auto
    define mp'' where "mp'' = mp_rx (filter (Not \<circ> f) (rx1 @ rx2), b)" 
    have eq: "deleted = add_mset (t, Var x) mp''" 
      unfolding deleted_def mp''_def rx mp_rx_def List.maps_def mset_concat_union using nf ts by auto
    have "\<exists> x mp''. xt = Var x \<and> deleted = add_mset (t, Var x) mp'' \<and> x \<notin> \<Union> (vars ` snd ` (mp_mset mp'' \<union> mp_mset mp'))" 
    proof (intro exI conjI, rule xt, rule eq, intro notI)
      assume "x \<in> \<Union> (vars ` snd ` (mp_mset mp'' \<union> mp_mset mp'))" 
      then obtain s t' where st: "(s,t') \<in> mp_mset (mp' + mp'')" and xt: "x \<in> vars t'" by force
      from xrx have "(s,t') \<notin> mp_mset mp''" using xt unfolding mp''_def mp_rx_def by force
      with st have "(s,t') \<in> mp_mset mp'" by auto
      with xxs have "(s, t') \<in># mp_rx (filter f rx, b)" using xt unfolding xs_def mp'_def mp_rx_def
        by auto
      with xt nf show False unfolding mp_rx_def f_def split ts list.sel 
        by auto (metis Un_iff \<open>\<not> (tl ts \<noteq> [] \<or> x \<in> set xs)\<close> fst_conv image_eqI prod.inject rx set_ConsD set_append ts xrx)
    qed
  } note lin_vars = this
  show "(\<rightarrow>\<^sub>m)\<^sup>*\<^sup>* (mp_lr mp) (mp_lr mpFin)" unfolding mpFin mp mp'(1) using lin_vars
  proof (induct deleted)
    case (add pair deleted)
    obtain t xt where pair: "pair = (t,xt)" by force
    hence "(t,xt) \<in># add_mset pair deleted" by auto
    from add(2)[OF this] pair
    obtain x where "add_mset pair deleted + mp' = add_mset (t, Var x) (deleted + mp')" 
      and x: "x \<notin> \<Union> (vars ` snd ` (mp_mset (deleted + mp')))" 
      and pair: "pair = (t, Var x)" 
      by auto  
    from match_match[OF this(2), of t, folded this(1)]
    have one: "add_mset pair deleted + mp' \<rightarrow>\<^sub>m (deleted + mp')" .
    have two: "(\<rightarrow>\<^sub>m)\<^sup>*\<^sup>* (deleted + mp') mp'" 
    proof (rule add(1), goal_cases)
      case (1 s yt)
      hence "(s,yt) \<in># add_mset pair deleted" by auto
      from add(2)[OF this]
      obtain y mp'' where yt: "yt = Var y" "add_mset pair deleted = add_mset (s, Var y) mp''"
         "y \<notin> \<Union> (vars ` snd ` (mp_mset mp'' \<union> mp_mset mp'))" 
        by auto
      from 1[unfolded yt] have "y \<in> \<Union> (vars ` snd ` (mp_mset (deleted + mp')))" by force
      with x have "x \<noteq> y" by auto
      with pair yt have "pair \<noteq> (s,Var y)" by auto
      with yt(2) have del: "deleted = add_mset (s, Var y) (mp'' - {#pair#})"
        by (meson add_eq_conv_diff)
      show ?case 
        by (intro exI conjI, rule yt, rule del, rule contra_subsetD[OF _ yt(3)]) 
         (intro UN_mono, auto dest: in_diffD)
    qed
    from one two show ?case by auto
  qed auto
  show "lvars_mp (mp_lr mpFin) \<subseteq> lvars_mp (mp_lr mp)" 
    unfolding mp mp' deleted_def mp'_def mpFin
    by (auto simp: lvars_mp_def mp_lr_def)
  show "set xs = lvars_mp (mp_list (mp_lx (fst mpFin)))" 
    unfolding mpFin 
    unfolding xs_def lvars_mp_def mp3
    unfolding match_var_impl_def split snd_conv fst_conv Let_def
    by auto
qed

lemma match_steps_impl: assumes "match_steps_impl mp = res" 
  shows "res = Some (xs,mp') \<Longrightarrow> (\<rightarrow>\<^sub>m)\<^sup>*\<^sup>* (mp_list mp) (mp_lr mp') \<and> wf_lr2 mp' 
     \<and> lvars_mp (mp_list mp) \<supseteq> lvars_mp (mp_lr mp')
     \<and> set xs = lvars_mp (mp_list (mp_lx (fst mp')))" 
    and "res = None \<Longrightarrow> \<exists> mp'. (\<rightarrow>\<^sub>m)\<^sup>*\<^sup>* (mp_list mp) mp' \<and> match_fail mp'" 
proof (atomize (full), goal_cases)
  case 1
  obtain res' where decomp: "decomp_impl mp = res'" by auto
  note res = assms[unfolded match_steps_impl_def decomp]
  note decomp = decomp_impl[OF decomp, of _ "{#}", unfolded empty_neutral]
  show ?case
  proof (cases res')
    case None
    with decomp res show ?thesis by auto
  next
    case (Some mp'')
    with decomp[of mp'']
    have steps: "(\<rightarrow>\<^sub>m)\<^sup>*\<^sup>* (mp_list mp) (mp_lr mp'')" and wf: "wf_lr mp''" 
      and lsub: "lvars_mp (mp_lr mp'') \<subseteq> lvars_mp (mp_list mp)" by auto
    from res[unfolded Some] have "res = Some (match_var_impl mp'')" by auto
    with match_var_impl[OF wf] steps res lsub show ?thesis
      by (cases "match_var_impl mp''", auto)
  qed
qed

lemma finite_sort_imp_finite_sort_vars: 
  assumes "t : \<sigma> in \<T>(C,\<V>)" 
  and "x \<in> vars t" 
  and "\<not> inf_sort \<sigma>" 
shows "\<not> inf_sort (snd x)"
  using assms
proof (induct)
  case (Fun f ts \<sigma>s \<sigma>)
  from Fun obtain t where "t \<in> set ts" and "x \<in> vars t" by auto
  then obtain i where i: "i < length ts" and x: "x \<in> vars (ts ! i)" by (auto simp: set_conv_nth)              
  from Fun(2)[unfolded list_all2_conv_all_nth] 
  have len: "length \<sigma>s = length ts" by auto
  from C_sub_S[OF Fun(1)] have inS: "\<sigma> \<in> S" "set \<sigma>s \<subseteq> S" by auto
  hence \<sigma>s: "\<And> j. j < length ts \<Longrightarrow> \<sigma>s ! j \<in> S" using len unfolding set_conv_nth by auto
  show ?case
  proof (rule list_all2_nthD[OF Fun(3) i, rule_format, OF x])
    show "\<not> inf_sort (\<sigma>s ! i)" unfolding inf_sort[OF \<sigma>s[OF i]] finite_sort_def
    proof 
      assume inf: "infinite {t. t : \<sigma>s ! i in \<T>(C)}" 
      {
        fix j
        assume "j < length ts" 
        from \<sigma>s[OF this] have "\<sigma>s ! j \<in> S" by auto
        from sorts_non_empty[OF this] have "\<exists> tj. tj : \<sigma>s ! j in \<T>(C)" by blast 
      }
      hence "\<forall> j. \<exists> tj. j < length ts \<longrightarrow> tj : \<sigma>s ! j in \<T>(C)" by auto
      from choice[OF this] obtain tj where 
        tj: "j < length ts \<Longrightarrow> tj j : \<sigma>s ! j in \<T>(C)" for j by auto
      define ft where "ft t = Fun f (map (tj (i := t)) [0..< length ts])" for t
      {
        fix t
        assume "t : \<sigma>s ! i in \<T>(C)" 
        hence "ft t : \<sigma> in \<T>(C)" unfolding ft_def using tj
          by (intro Fun_hastypeI[OF Fun(1)] list_all2_all_nthI, auto simp: len)
      } note ft = this
      have inj: "inj ft" unfolding ft_def using i by (auto simp: inj_def)
      from inf inj have "infinite (ft ` {t. t : \<sigma>s ! i in \<T>(C)})"
        by (metis finite_imageD inj_def inj_on_def)
      with ft have "infinite {t. t : \<sigma> in \<T>(C)}"
        by (metis (no_types, lifting) finite_subset image_subset_iff mem_Collect_eq)
      with Fun(5) inf_sort[OF inS(1)] 
      show False unfolding finite_sort_def by auto
    qed
  qed
qed auto


context 
  fixes CC :: "'f \<times> 's list \<Rightarrow> 's option" 
    and renVar :: "'v \<Rightarrow> 'v" 
    and renNat  :: "nat \<Rightarrow> 'v" 
    and fidl_solver :: "((nat\<times>'s) \<times> int)list \<times> _ \<Rightarrow> bool" 
  assumes CC: "improved \<Longrightarrow> CC = C" 
    and renaming_ass: "improved \<Longrightarrow> renaming_funs renNat renVar" 
    and fidl_solver: "improved \<Longrightarrow> finite_idl_solver fidl_solver"
begin

abbreviation Match_decomp'_impl where "Match_decomp'_impl \<equiv> match_decomp'_impl renNat" 
abbreviation Decomp'_main_loop where "Decomp'_main_loop \<equiv> decomp'_main_loop renNat" 
abbreviation Decomp'_impl where "Decomp'_impl \<equiv> decomp'_impl renNat" 
abbreviation Pat_inner_impl where "Pat_inner_impl \<equiv> pat_inner_impl renNat" 
abbreviation Pat_impl where "Pat_impl \<equiv> pat_impl CC renNat" 
abbreviation Pats_impl where "Pats_impl \<equiv> pats_impl CC renNat fidl_solver" 
abbreviation Pat_complete_impl where "Pat_complete_impl \<equiv> pat_complete_impl CC renNat renVar fidl_solver"

definition allowed_vars where "allowed_vars n = (if improved then range renVar \<union> renNat ` {..<n} else UNIV)" 

definition lvar_cond where "lvar_cond n V = (V \<subseteq> allowed_vars n)"
definition lvar_cond_mp where "lvar_cond_mp n mp = lvar_cond n (lvars_mp mp)" 
definition lvar_cond_pp where "lvar_cond_pp n pp = lvar_cond n (lvars_pp pp)" 

lemma lvar_cond_simps[simp]: 
  "lvar_cond n (insert x A) = (x \<in> allowed_vars n \<and> lvar_cond n A)" 
  "lvar_cond n {}" 
  "lvar_cond n (A \<union> B) = (lvar_cond n A \<and> lvar_cond n B)" 
  "lvar_cond n (\<Union> As) = (\<forall> A \<in> As. lvar_cond n A)" 
  unfolding lvar_cond_def by auto

lemma lvar_cond_mono: "n \<le> n' \<Longrightarrow> lvar_cond n V \<Longrightarrow> lvar_cond n' V" 
  unfolding lvar_cond_def allowed_vars_def by (auto split: if_splits)

(* begin: move into suitable position *)
lemma pair_fst_imageI: "(a,b) \<in> c \<Longrightarrow> a \<in> fst ` c" by force

lemma not_in_fstD: "x \<notin> fst ` a \<Longrightarrow> \<forall> z. (x,z) \<notin> a" by force

lemma many_remdups_steps: assumes "mp_mset mp2 = mp_mset mp1" "mp2 \<subseteq># mp1"
  shows "(\<rightarrow>\<^sub>m)\<^sup>*\<^sup>* mp1 mp2"
proof -
  from assms obtain mp3 where mp1: "mp1 = mp3 + mp2"
    by (metis subset_mset.less_eqE union_commute)
  from assms(1)[unfolded mp1] have "mp_mset mp3 \<subseteq> mp_mset mp2" by auto
  thus ?thesis unfolding mp1
  proof (induct mp3)
    case (add pair mp3)
    from add have IH: "(\<rightarrow>\<^sub>m)\<^sup>*\<^sup>* (mp3 + mp2) mp2" by auto
    from add have "pair \<in># mp3 + mp2" by auto
    then obtain mp4 where "mp3 + mp2 = add_mset pair mp4" by (rule mset_add)
    from match_duplicate[of pair mp4, folded this] IH
    show ?case by simp
  qed auto
qed

lemma many_match_steps: 
  assumes "\<And> t l. (t,l) \<in># mp1 \<Longrightarrow> \<exists> x. l = Var x \<and> x \<notin> lvars_mp (mp1 - {# (t,l) #} + mp2)" 
  shows "(\<rightarrow>\<^sub>m)\<^sup>*\<^sup>* (mp1 + mp2) mp2" 
  using assms
proof (induct mp1)
  case (add pair mp1)
  obtain t l where pair: "pair = (t, l)" by force
  from add(2)[of t l, unfolded pair] obtain x where 
    l: "l = Var x" and x: "x \<notin> lvars_mp (mp1 + mp2)" 
    by auto
  from match_match[of x "mp1 + mp2" t, folded l, folded pair]
  have "add_mset pair (mp1 + mp2) \<rightarrow>\<^sub>m mp1 + mp2" using x unfolding lvars_mp_def by auto
  also have "(\<rightarrow>\<^sub>m)\<^sup>*\<^sup>* (mp1 + mp2) mp2" 
    by (rule add, insert add(2), force simp: lvars_mp_def)
  finally show ?case by simp
qed auto

(* end: move out of context *)

lemma decomp'_impl: assumes 
    "wf_lr2 mp" 
    "set xs = lvars_mp (mp_list (mp_lx (fst mp)))" 
    "lvar_cond_mp n (mp_lr mp)"
    "Decomp'_impl n xs mp = (n',mp')" 
    improved
  shows "wf_lr3 mp'" 
    "lvar_cond_mp n' (mp_lr mp')"
    "(\<rightarrow>\<^sub>m)\<^sup>*\<^sup>* (mp_lr mp) (mp_lr mp')" 
    "n \<le> n'" 
proof (atomize (full), goal_cases)
  case 1
  obtain xl rx b where mp: "mp = (xl,rx,b)" by (cases mp, auto)
  define out where "out = ([] :: ('v,('f,nat \<times> 's)term list) alist)" 
  let ?lr = "\<lambda> rx. (xl,rx,b)" 
  define Measure where "Measure (rx :: ('v,('f,nat \<times> 's)term list) alist) = 
    sum_list (map ((\<lambda> ts. sum_list (map size ts)) o snd) rx)" for rx
  define cond3 where "cond3 ts = (xl = [] \<longrightarrow> wf_ts3 ts)" for ts 
  {
    fix out rx'
    assume "Decomp'_main_loop n xs rx out = (n', rx')" 
      "wf_lr2 (?lr (rx @ out))" 
      "lvar_cond_mp n (mp_lr (?lr (rx @ out)))" 
      "Ball (snd ` set out) cond3" 
    hence "wf_lr3 (?lr rx') \<and> lvar_cond_mp n' (mp_lr (?lr rx')) 
      \<and> (\<rightarrow>\<^sub>m)\<^sup>*\<^sup>* (mp_lr (?lr (rx @ out))) (mp_lr (?lr rx'))
      \<and> n \<le> n'"
    proof (induct rx arbitrary: n n' out rx' rule: wf_induct[OF wf_measure[of Measure]])
      case (1 rx n n' out rx')
      note IH = 1(1)[rule_format]
      have "Decomp'_main_loop n xs rx out = (n', rx')" by fact
      note res = this[unfolded decomp'_main_loop.simps[of _ _ _ rx]]
      note wf = 1(3)
      note lvc = 1(4)
      note cond3 = 1(5)
      show ?case 
      proof (cases rx)
        case Nil
        from Nil have mset: "mset (rx @ out) = mset out" by auto (* or: mset (rev out) *)
        note wf = wf[unfolded wf_lr2_mset[OF mset]]
        note mp_lr = mp_lr_mset[OF mset]
        show ?thesis using Nil wf lvc res cond3 unfolding mp_lr
          by (auto simp: wf_lr3_def wf_lr2_def wf_rx3_def cond3_def)
      next
        case (Cons pair rx2)
        then obtain x ts where rx: "rx = (x,ts) # rx2" by (cases pair, auto)        
        let ?cond = "tl ts = [] \<or> (\<exists> t \<in> set ts. is_Var t) \<or> x \<in> set xs" 
        note res = res[unfolded rx split list.simps]
        from wf[unfolded rx wf_lr2_def split] have wfts: "wf_ts ts \<or> wf_ts2 ts" 
          and dist_vars: "distinct (x # map fst (rx2 @ out))" 
          by (auto simp: wf_rx_def wf_rx2_def split: if_splits)
        hence ts: "ts \<noteq> []" unfolding wf_ts_def wf_ts2_def by auto
        show ?thesis
        proof (cases ?cond)
          case True
          hence "?cond = True" by simp
          note res = res[unfolded this if_True]
          have mset: "mset (rx @ out) = mset (rx2 @ (x, ts) # out)" unfolding rx by auto
          note wf = wf[unfolded wf_lr2_mset[OF mset]]
          note mp_lr = mp_lr_mset[OF mset]
          have c3: "cond3 ts" 
            unfolding cond3_def
          proof (intro impI)
            assume xl: "xl = []" 
            with assms[unfolded mp] have xs: "xs = []" unfolding lvars_mp_def by auto
            from wf[unfolded wf_lr2_def split] xl have "wf_ts2 ts" unfolding wf_rx2_def by auto
            hence "tl ts \<noteq> []" unfolding wf_ts2_def by (cases ts, auto)
            with True xs have "\<exists>t\<in>set ts. is_Var t" by auto
            thus "wf_ts3 ts" unfolding wf_ts3_def by auto
          qed
          have "(rx2, rx) \<in> measure Measure" unfolding Measure_def rx using ts
            by (cases ts, auto) 
          note IH = IH[OF this res wf lvc[unfolded mp_lr], folded mp_lr]
          show ?thesis 
            by (rule IH, insert c3 cond3, auto)
        next
          case False
          define l where "l = num_args (hd ts)"
          define k where "k = length ts" 
          define fresh where "fresh = map renNat [n..<n + l]" 
          define rx1 where "rx1 = zipAll fresh (map args ts)"
          from ts have 0: "0 < length ts" and k0: "k \<noteq> 0" by (auto simp: k_def)
          from ts have "hd ts \<in> set ts" by auto
          with False obtain f bs0 where hd: "hd ts = Fun f bs0" by blast
          from False ts have k: "k \<ge> 2" unfolding k_def by (cases ts; cases "tl ts"; auto)
          hence l0: "l = length bs0" unfolding l_def using ts hd by auto
          from ts hd have ts0: "ts ! 0 = Fun f bs0" by (cases ts, auto)
          from wfts[unfolded wf_ts_def wf_ts2_def]
          have dist_noconf: "distinct ts \<and> (\<forall> j. 0 < j \<longrightarrow> j < length ts \<longrightarrow> conflicts (ts ! 0) (ts ! j) \<noteq> None)" by auto
          have lfresh: "length fresh = l" unfolding fresh_def by simp
          from renaming_ass[unfolded renaming_funs_def, rule_format, OF \<open>improved\<close>] 
          have ren: "inj renNat" "inj renVar" "range renNat \<inter> range renVar = {}" by auto
          {
            fix t
            assume tts: "t \<in> set ts" 
            from False tts obtain g bs where t: "t = Fun g bs" by (cases t, auto)
            with tts obtain i where i: "i < length ts" and tsi: "ts ! i = Fun g bs" 
              unfolding set_conv_nth by auto
            have "length bs = l \<and> g = f" 
            proof (cases "i = 0")
              case True
              with ts0 l0 tsi show ?thesis by auto
            next
              case False
              with i dist_noconf have "conflicts (ts ! 0) (ts ! i) \<noteq> None" by auto
              from this[unfolded tsi ts0] l0 show ?thesis 
                by (auto simp: conflicts.simps split: if_splits)
            qed
            with t tts have "\<exists> bs. t = Fun f bs \<and> length bs = l" by auto  
          } note no_conflict = this
          define t where "t = (\<lambda> i j. args (ts ! i) ! j)"
          have "ts = map (\<lambda> i. ts ! i) [0..<k]" unfolding k_def 
            by (intro nth_equalityI, auto)
          also have "\<dots> = map (\<lambda> i. Fun f (map (t i) [0 ..< l])) [0..<k]" 
          proof (intro map_cong[OF refl])
            fix i
            assume "i \<in> set [0..<k]" 
            hence "ts ! i \<in> set ts" unfolding k_def by auto
            from no_conflict[OF this] obtain bs where tsi: "ts ! i = Fun f bs" and 
              len: "length bs = l" by auto
            show "ts ! i = Fun f (map (t i) [0..<l])" unfolding tsi term.simps term.sel t_def 
              using len by (intro conjI nth_equalityI, auto)
          qed
          finally have ts_t: "ts = map (\<lambda>i. Fun f (map (t i) [0..<l])) [0..<k]" .  
          {
            fix bs
            assume "bs \<in> set (map args ts)" 
            hence "length bs = l" using no_conflict by force
          }
          from zipAll[OF lfresh, of "map args ts", OF this, unfolded map_map o_def, folded rx1_def]
          have "rx1 = map (\<lambda>j. (fresh ! j, map (\<lambda>bs. bs ! j) (map args ts))) [0..<l]" by auto
          also have "\<dots> = map (\<lambda>i. (fresh ! i, map (\<lambda> j. t j i) [0..<k])) [0..<l]" 
            by (intro nth_equalityI, auto simp: ts_t)
          finally have rx1: "rx1 = map (\<lambda>i. (fresh ! i, map (\<lambda> j. t j i) [0..<k])) [0..<l]" .
          define rrx where "rrx = map (\<lambda>(y, ts'). (y, remdups ts')) rx1" 
          define frrx where "frrx = filter (\<lambda>(y, ts'). tl ts' \<noteq> []) rrx" 
          from False have "?cond = False" by simp
          note res = res[unfolded this if_False, folded l_def, 
              unfolded Let_def, folded fresh_def, folded rx1_def, folded rrx_def, folded frrx_def]
          (* decrease in measure *)
          let ?meas = "\<lambda> rx. sum_list (map ((\<lambda>ts. sum_list (map size ts)) \<circ> snd) rx)" 
          have snd_case: "snd (case x of (y :: 'v, ts') \<Rightarrow> (y, remdups ts')) = remdups (snd x)" for x by (cases x, auto)
          have fst_case: "fst (case x of (y :: 'v, ts') \<Rightarrow> (y, remdups ts')) = fst x" for x by (cases x, auto)
          have sum_remdups: "sum_list (map size (remdups b)) \<le> sum_list (map size b)" for b by (induct b, auto)
          have "?meas frrx \<le> ?meas rrx" unfolding frrx_def by (induct rrx, auto)
          also have "\<dots> \<le> ?meas rx1" unfolding rrx_def 
            by (induct rx1, auto simp: o_def split: prod.splits intro!: add_mono sum_remdups)
          also have "\<dots> = (\<Sum>x\<leftarrow>[0..<l]. \<Sum>xa\<leftarrow>[0..<k]. size (t xa x))" 
            unfolding rx1 map_map o_def snd_conv by simp
          also have "\<dots> = (\<Sum>xa\<leftarrow>[0..<k]. \<Sum>x\<leftarrow>[0..<l]. size (t xa x))" 
            unfolding sum.list_conv_set_nth by (auto intro: sum.swap)
          also have "\<dots> < sum_list (map size ts)" 
            unfolding ts_t map_map o_def
            by (intro sum_list_strict_mono, insert k0, auto simp: o_def size_list_conv_sum_list)
          finally have measure: "(frrx @ rx2, rx) \<in> measure Measure" unfolding Measure_def rx
            by simp

          (* single step *)
          have left: "mp_lr (xl, rx @ out, b) = mp_rx ([(x,ts)],b) + mp_lr (xl, rx2 @ out, b)" 
            unfolding mp_lr_def split mp_rx_def rx by (auto simp: List.maps_def)
          have right: "mp_lr (xl, (rx1 @ rx2) @ out, b) = mp_rx (rx1 ,b) + mp_lr (xl, rx2 @ out, b)" 
            unfolding mp_lr_def split mp_rx_def rx by (auto simp: List.maps_def)
          have cong: "mp0 + mp2 \<rightarrow>\<^sub>m mp1 + mp2 \<Longrightarrow> mp1 = mp1' \<Longrightarrow> mp0 + mp2 \<rightarrow>\<^sub>m mp1' + mp2"  
            for mp0 mp2 mp1 mp1' :: "('f,'v,'s)match_problem_mset" by auto
          note List.maps_def[simp]
          from assms(2)[unfolded mp] 
          have xs: "set xs = lvars_mp (mp_list (mp_lx xl))" by auto
          have dist_fresh: "distinct fresh" unfolding fresh_def distinct_map
            using ren by (auto simp: inj_def inj_on_def)
          have lvars_fresh_disj: "lvars_mp (mp_lr (xl, rx @ out, b)) \<inter> set fresh = {}" 
          proof -
            have "lvars_mp (mp_lr (xl, rx @ out, b)) \<subseteq> allowed_vars n" 
              using 1(4) unfolding lvar_cond_mp_def lvar_cond_def .
            moreover have "set fresh \<inter> allowed_vars n = {}" unfolding allowed_vars_def fresh_def
              using ren(3) \<open>improved\<close>
              by (auto dest: injD[OF ren(1)]) 
            ultimately show ?thesis by auto
          qed          
          have step: "mp_lr (xl, rx @ out, b) \<rightarrow>\<^sub>m mp_lr (xl, (rx1 @ rx2) @ out, b)" 
            unfolding left right 
          proof (rule cong[OF match_decompose'[OF _ _ _ lfresh _ \<open>improved\<close>, of _ x f]])
            show "(ti, y) \<in># mp_rx ([(x, ts)], b) \<Longrightarrow> y = Var x \<and> root ti = Some (f, l)" for ti y
              unfolding ts_t mp_rx_def by auto
            from False have xxs: "x \<notin> set xs" by auto
            show "(ti, y) \<in># mp_lr (xl, rx2 @ out, b) \<Longrightarrow> x \<notin> vars y" for ti y
              using dist_vars xxs[unfolded xs] 
              by (auto simp: mp_lr_def lvars_mp_def mp_rx_def dest: pair_fst_imageI)            
            have var_id: "\<Union> (vars ` snd ` mp_mset (mp_rx ([(x, ts)], b) + mp_lr (xl, rx2 @ out, b)))
              = lvars_mp (mp_lr (xl, rx @ out, b))" 
              unfolding rx lvars_mp_def mp_rx_def mp_lr_def split by auto
            show "lvars_disj_mp fresh (mp_mset (mp_rx ([(x, ts)], b) + mp_lr (xl, rx2 @ out, b)))" 
              unfolding lvars_disj_mp_def var_id
            proof
              show "distinct fresh" by fact
              have "lvars_mp (mp_lr (xl, rx @ out, b)) \<subseteq> allowed_vars n" 
                using 1(4) unfolding lvar_cond_mp_def lvar_cond_def .
              moreover have "set fresh \<inter> allowed_vars n = {}" unfolding allowed_vars_def fresh_def
                using ren(3) \<open>improved\<close>
                by (auto dest: injD[OF ren(1)]) 
              ultimately show "lvars_mp (mp_lr (xl, rx @ out, b)) \<inter> set fresh = {}" by auto
            qed
            show "2 \<le> size (mp_rx ([(x, ts)], b))" 
              using k[unfolded k_def] unfolding mp_rx_def by auto
            define aux where "aux i j = (t j i, Var (fresh ! i) :: ('f,'v)term)" for i j
            have fresh_index: "map Var fresh = map (\<lambda> i. Var (fresh ! i)) [0..<l]" 
              unfolding lfresh[symmetric]
              by (intro nth_equalityI, auto)
            have "(\<Sum>(t, l)\<in>#mp_rx ([(x, ts)], b). mp_list (zip (args t) (map Var fresh)))
              = mset (concat (map (\<lambda> t. zip (args t) (map Var fresh)) ts))" 
              unfolding mp_rx_def by (induct ts, auto)
            also have "\<dots> = mset (concat (map (\<lambda> j. map (\<lambda> i. (t j i,Var (fresh ! i))) [0..<l]) [0..<k]))" 
              unfolding ts_t map_map o_def
              apply (intro arg_cong[of _ _ mp_list])
              apply (intro arg_cong[of _ _ concat])
              apply (intro map_cong[OF refl])
              apply (subst zip_nth_conv)
              by (auto simp: fresh_def)
            also have "\<dots> = mp_rx (rx1, b)"
              unfolding mp_rx_def 
              by (auto simp add: rx1 o_def fresh_index ts_t mset_concat_union intro: mset_sum_reindex)
            finally show "(\<Sum>(t, l)\<in>#mp_rx ([(x, ts)], b). mp_list (zip (args t) (map Var fresh))) =
              mp_rx (rx1, b)" .
          qed
          (* invariant preservation *) 
          have rrx_seteq: "mp_mset (mp_rx (rrx, b)) = mp_mset (mp_rx (rx1, b))" 
            unfolding mp_rx_def rrx_def by (induct rx1, auto simp: o_def mset_concat)
          have glob_rrx_set_eq: "mp_mset (mp_lr (xl, (rx1 @ rx2) @ out, b)) = mp_mset (mp_lr (xl, (rrx @ rx2) @ out, b))" 
            unfolding mp_lr_def split mp_rx_append using rrx_seteq by auto
          have frrx_sub: "mp_mset (mp_rx (frrx, b)) \<subseteq> mp_mset (mp_rx (rx1, b))" 
            unfolding rrx_seteq[symmetric]
            unfolding mp_rx_def frrx_def by (induct rrx, auto simp: o_def mset_concat)
          have glob_rrx_sub: "mp_mset (mp_lr (xl, (frrx @ rx2) @ out, b)) \<subseteq> mp_mset (mp_lr (xl, (rx1 @ rx2) @ out, b))" 
            unfolding mp_lr_def split mp_rx_append using frrx_sub by auto
          (* left-var condition *)
          have lvc': "lvar_cond_mp (n + l) (mp_lr (xl, (rx1 @ rx2) @ out, b))" 
            unfolding lvar_cond_mp_def lvar_cond_def
          proof
            fix y
            have rx': "rx = [(x,ts)] @ rx2" unfolding rx by auto
            assume "y \<in> lvars_mp (mp_lr (xl, (rx1 @ rx2) @ out, b))" 
            hence "y \<in> lvars_mp (mp_lr (xl, rx @ out, b)) \<or> y \<in> lvars_mp (mp_rx (rx1,b))" 
              unfolding rx' 
              unfolding mp_lr_def split lvars_mp_def mp_rx_append by auto
            thus "y \<in> allowed_vars (n + l)" 
            proof
              assume "y \<in> lvars_mp (mp_lr (xl, rx @ out, b))" 
              with lvc have "y \<in> allowed_vars n" unfolding lvar_cond_mp_def lvar_cond_def by auto
              thus ?thesis unfolding allowed_vars_def by auto
            next
              assume "y \<in> lvars_mp (mp_rx (rx1, b))" 
              hence "y \<in> set fresh" unfolding rx1 lvars_mp_def mp_rx_def List.maps_def
                using lfresh by auto
              thus ?thesis unfolding fresh_def by (auto simp: allowed_vars_def)
            qed
          qed    
          have "lvars_mp (mp_lr (xl, (frrx @ rx2) @ out, b)) \<subseteq> lvars_mp (mp_lr (xl, (rx1 @ rx2) @ out, b))" 
            using glob_rrx_sub
            unfolding lvars_mp_def by auto
          hence lvar_cond_new: "lvar_cond_mp (n + l) (mp_lr (xl, (frrx @ rx2) @ out, b))" 
            using lvc' unfolding lvar_cond_mp_def lvar_cond_def by auto

          have wflx: "wf_lx xl" using wf unfolding wf_lr2_def by auto
          define ro where "ro = rx @ out" 
          (* distinctness *)
          from wf[unfolded wf_lr2_def wf_rx2_def wf_rx_def]
          have dist_old: "distinct (map fst (rx @ out))" by (auto split: if_splits)
          have dist_mid: "distinct (map fst ((rx1 @ rx2) @ out))" 
          proof -
            from dist_old have "distinct (map fst (rx2 @ out))" by (simp add: rx)
            moreover have "set (map fst (rx2 @ out)) \<inter> set fresh = {}" 
            proof (rule ccontr)
              assume "\<not> ?thesis"
              then obtain y where y: "y \<in> set (map fst (rx2 @ out))" "y \<in> set fresh" by auto
              from y obtain ts where yts: "(y,ts) \<in> set (rx @ out)" by (force simp: rx)
              hence "ts \<in> snd ` set (rx @ out)" by force
              with wf[unfolded wf_lr_def wf_lr2_def wf_rx2_def wf_rx_def split fst_conv]
              have "wf_ts ts \<or> wf_ts2 ts" by metis
              with this[unfolded wf_ts_def wf_ts2_def] obtain t ts' where ts: "ts = t # ts'" by (cases ts, auto)
              from yts[unfolded this] have "y \<in> lvars_mp (mp_rx (rx @ out, b))" 
                unfolding lvars_mp_def mp_rx_def split fst_conv ro_def[symmetric]
                unfolding lvars_mp_def mp_lr_def mp_rx_def rx by force
              hence "y \<in> lvars_mp (mp_lr (xl, rx @ out, b))" unfolding lvars_mp_def mp_lr_def by auto
              with lvars_fresh_disj have "y \<notin> set fresh" by auto
              with y show False by auto
            qed
            moreover have "map fst rx1 = fresh" unfolding rx1 using lfresh 
              by (intro nth_equalityI, auto)
            ultimately show ?thesis using dist_fresh by auto
          qed
          also have "map fst ((rx1 @ rx2) @ out) = map fst ((rrx @ rx2) @ out)" 
            unfolding rrx_def by auto
          finally have dist_new: "distinct (map fst ((frrx @ rx2) @ out)) = True" 
            unfolding frrx_def by (auto simp: distinct_map_filter)

          (* b-values = inf-var-conflicts *)  
          from wf[unfolded rx wf_lr2_def split wf_rx2_def wf_rx_def fst_conv]
          have wf_ts: "wf_ts ts \<or> wf_ts2 ts" by (auto split: if_splits)
          {
            fix i j
            assume ij: "i < k" "j < k" 
            from wf_ts[unfolded wf_ts_def wf_ts2_def] ij
            have "conflicts (ts ! i) (ts ! j) \<noteq> None \<or> conflicts (ts ! j) (ts ! i) \<noteq> None" 
              unfolding k_def by (cases "i < j"; cases "i = j"; auto)
            with conflicts_sym have "conflicts (ts ! i) (ts ! j) \<noteq> None" 
              by (metis rel_option_None2)
          } note ts_no_conflict = this
          let ?old = "mp_rx (rx @ out, b)" 
          let ?mid = "mp_rx ((rx1 @ rx2) @ out, b)" 
          let ?new = "mp_rx ((frrx @ rx2) @ out, b)" 
          have "mp_mset (mp_rx (frrx, b)) \<le> mp_mset (mp_rx (rrx, b))" 
            unfolding mp_rx_def frrx_def by auto
          also have rrx_rx1: "\<dots> \<subseteq> mp_mset (mp_rx (rx1, b))"
            unfolding mp_rx_def rrx_def by auto
          finally have frrx_sub_rx1: "mp_mset (mp_rx (frrx, b)) \<subseteq> mp_mset (mp_rx (rx1, b))" .
          hence new_sub_mid: "mp_mset ?new \<subseteq> mp_mset ?mid" unfolding mp_rx_append by auto

          have b_correct: "(b = inf_var_conflict (mp_mset ?new)) = True" 
          proof -
            let ?old = "mp_rx (rx @ out, b)" 
            let ?mid = "mp_rx ((rx1 @ rx2) @ out, b)" 
            let ?new = "mp_rx ((frrx @ rx2) @ out, b)" 
            from wf[unfolded wf_lr2_def wf_rx2_def wf_rx_def]  
            have "b = inf_var_conflict (mp_mset ?old)" by (auto split: if_splits)
            also have "\<dots> = inf_var_conflict (mp_mset ?new)" (is "?inf_old = ?inf_new")
            proof
              assume ?inf_old 
              from this[unfolded inf_var_conflict_def]
              obtain u w y z where
                u: "(u, Var y) \<in># ?old" and
                w: "(w, Var y) \<in># ?old" and
                conf: "Conflict_Var u w z" and
                inf: "inf_sort (snd z)"  by auto
              show ?inf_new
              proof (cases "y = x")
                case False
                hence "(u, Var y) \<in># ?new" "(w, Var y) \<in># ?new" using u w 
                  unfolding rx mp_rx_append mp_rx_Cons split by auto
                with conf inf show ?thesis unfolding inf_var_conflict_def by blast
              next
                case True
                with dist_old u w have uw_ts: "u \<in> set ts" "w \<in> set ts" 
                  unfolding rx mp_rx_Cons mp_rx_append split 
                  by (auto simp: mp_rx_def dest!: not_in_fstD)
                with conf have uw: "u \<noteq> w" by auto 
                from uw_ts(1) obtain i where i: "i < k" and u: "u = ts ! i" 
                  unfolding k_def by (auto simp: set_conv_nth)
                from uw_ts(2) obtain j where j: "j < k" and w: "w = ts ! j" 
                  unfolding k_def by (auto simp: set_conv_nth)
                from u w uw have ij: "i \<noteq> j" by auto
                have id: "((f, length [0..<l]) = (f, length [0..<l])) = True" by simp
                have "Conflict_Var (Fun f (map (t i) [0..<l])) (Fun f (map (t j) [0..<l])) z" 
                  using conf[unfolded u w ts_t] i j by auto
                note * = this[unfolded conflicts.simps length_map id if_True] 
                from * obtain cs where those: "those (map2 conflicts (map (t i) [0..<l]) (map (t j) [0..<l])) = Some cs" (is "?th = _")
                  by (cases ?th, auto)
                from *[unfolded those] obtain c where c: "c \<in> set cs" and z: "z \<in> set c" by auto
                from arg_cong[OF those[unfolded those_eq_Some], of length] 
                have lcs: "length cs = l" by auto
                with c obtain a where a: "a < l" and c: "c = cs ! a" by (auto simp: set_conv_nth)
                from arg_cong[OF those[unfolded those_eq_Some], of "\<lambda> cs. cs ! a"]
                have "conflicts (t i a) (t j a) = Some c" using lcs a c by auto
                with z have conf: "Conflict_Var (t i a) (t j a) z" by auto
                hence diff: "t i a \<noteq> t j a" by auto
                let ?rd = "remdups (map (\<lambda>j. t j a) [0..<k])" 
                from i j have "t i a \<in> set ?rd" "t j a \<in> set ?rd" by auto
                with diff have tl: "tl (remdups (map (\<lambda>j. t j a) [0..<k])) \<noteq> []" 
                  by (cases "remdups (map (\<lambda>j. t j a) [0..<k])"; cases "tl (remdups (map (\<lambda>j. t j a) [0..<k]))", auto)
                have mem: "(t i a, Var (fresh ! a)) \<in># mp_rx (frrx,b) \<and> (t j a, Var (fresh ! a)) \<in># mp_rx (frrx,b)" 
                  unfolding frrx_def rrx_def rx1 using a i j tl
                  unfolding mp_rx_def map_map o_def split fst_conv List.maps_def in_multiset_in_set
                  by (intro conjI, auto intro!: bexI[of _ a])
                hence tia: "(t i a, Var (fresh ! a)) \<in># ?new"  
                  and tja: "(t j a, Var (fresh ! a)) \<in># ?new" unfolding mp_rx_append by auto
                from tia tja conf inf show ?thesis unfolding inf_var_conflict_def by blast
              qed
            next
              assume ?inf_new
              from this[unfolded inf_var_conflict_def]
              obtain u w y z where
                u: "(u, Var y) \<in># ?new" and
                w: "(w, Var y) \<in># ?new" and
                conf: "Conflict_Var u w z" and
                inf: "inf_sort (snd z)" by auto
              from u w new_sub_mid have u: "(u, Var y) \<in># ?mid" and w: "(w, Var y) \<in># ?mid" by auto
              show ?inf_old
              proof (cases "(u, Var y) \<in># mp_rx (rx2 @ out, b) \<and> (w, Var y) \<in># mp_rx (rx2 @ out, b)")
                case True
                hence "(u, Var y) \<in># ?old" "(w, Var y) \<in># ?old" using u w 
                  unfolding rx mp_rx_append mp_rx_Cons split by auto
                with conf inf show ?thesis unfolding inf_var_conflict_def by blast
              next
                case False
                then obtain v where "(v, Var y) \<in># mp_rx (rx1, b)" using u w
                  unfolding mp_rx_append rx by auto
                hence y: "y \<in> set (map fst rx1)" "y \<in> set fresh" unfolding rx1 mp_rx_def using lfresh by auto
                with dist_mid have yro: "y \<notin> fst ` set (rx2 @ out)" by auto
                from not_in_fstD[OF yro] u 
                have u: "(u,Var y) \<in># mp_rx (rx1, b)" unfolding mp_rx_def by auto
                from not_in_fstD[OF yro] w 
                have w: "(w,Var y) \<in># mp_rx (rx1, b)" unfolding mp_rx_def by auto
                from y obtain a where a: "a < l" and y: "y = fresh ! a" using lfresh by (auto simp: set_conv_nth)
                from u[unfolded mp_rx_def rx1] obtain a' i 
                  where u: "u = t i a'" "i < k" "y = fresh ! a'" "a' < l" 
                  by auto
                from y[unfolded u] have "a' = a" unfolding fresh_def using \<open>a' < l\<close> a
                  by (auto dest: injD[OF ren(1)])
                note u = u(1-2)[unfolded this]
                from w[unfolded mp_rx_def rx1] obtain a' j 
                  where w: "w = t j a'" "j < k" "y = fresh ! a'"  "a' < l" 
                  by auto
                from y[unfolded w] have "a' = a" unfolding fresh_def using \<open>a' < l\<close> a
                  by (auto dest: injD[OF ren(1)])
                note w = w(1-2)[unfolded this]
                from ts_no_conflict[OF u(2) w(2)] obtain cs where
                  conf_ij: "conflicts (ts ! i) (ts ! j) = Some cs" by auto
                hence "conflicts (Fun f (map (t i) [0..<l])) (Fun f (map (t j) [0..<l])) = Some cs" 
                  unfolding ts_t using u(2) w(2) by auto
                from this[unfolded conflicts.simps]
                have "map_option concat (those (map2 conflicts (map (t i) [0..<l]) (map (t j) [0..<l]))) = Some cs" 
                  by auto
                then obtain css where those: "those (map2 conflicts (map (t i) [0..<l]) (map (t j) [0..<l])) = Some css" 
                  and cs: "cs = concat css" by force
                from conf[unfolded u w] obtain csi where 
                  conf: "conflicts (t i a) (t j a) = Some csi" and z: "z \<in> set csi"
                  by auto
                from arg_cong[OF those[unfolded those_eq_Some], of length]
                have lcss: "length css = l" by auto
                from arg_cong[OF those[unfolded those_eq_Some], of "\<lambda> xs. xs ! a"] lcss conf z
                have "z \<in> set (css ! a)" using a by simp
                with lcss a cs have "z \<in> set cs" by auto
                with conf_ij have "Conflict_Var (ts ! i) (ts ! j) z" by auto
                moreover have "(ts ! i, Var x) \<in># ?old" using u(2) 
                  unfolding rx mp_rx_Cons mp_rx_append split k_def by auto
                moreover have "(ts ! j, Var x) \<in># ?old" using w(2) 
                  unfolding rx mp_rx_Cons mp_rx_append split k_def by auto
                ultimately show ?thesis using inf unfolding inf_var_conflict_def by blast
              qed
            qed
            finally show ?thesis 
              by (simp add: mp_rx_append rrx_seteq)
          qed

          (* no clashes *)
          {
            fix y ts' t1 t2 
            assume *: "(y,ts') \<in> set ((rx1 @ rx2) @ out)" "t1 \<in> set ts'" "t2 \<in> set ts'" 
            have "conflicts t1 t2 \<noteq> None" 
            proof
              assume conf: "conflicts t1 t2 = None" 
              hence diff: "t1 \<noteq> t2" by auto
              from conf have conf': "conflicts t2 t1 = None" using conflicts_sym[of t1 t2] by auto
              from *(2-3) obtain i where t1: "t1 = ts' ! i" and i: "i < length ts'" by (auto simp: set_conv_nth)
              from *(2-3) obtain j where t2: "t2 = ts' ! j" and j: "j < length ts'" by (auto simp: set_conv_nth)
              from diff i j t1 conf conf' obtain i j where 
                ij: "j < length ts'" "i < j" and 
                conf: "conflicts (ts' ! i) (ts' ! j) = None" 
                unfolding t1 t2
                by (cases "i < j"; cases "j < i"; auto)
              show False
              proof (cases "(y,ts') \<in> set rx1")
                case False
                hence "(y,ts') \<in> set (rx @ out)" using * unfolding rx by auto
                with wf[unfolded wf_lr2_def wf_rx2_def wf_rx_def] 
                have wf_ts: "wf_ts ts' \<or> wf_ts2 ts'" unfolding ro_def[symmetric] by (auto split: if_splits)
                with ij conf show False unfolding wf_ts_def wf_ts2_def by blast
              next
                case True
                from this[unfolded rx1] obtain a where a: "a < l" 
                  and ts': "ts' = map (\<lambda>j. t j a) [0..<k]"
                  and lts': "length ts' = k" by auto
                from conf have conf: "conflicts (t i a) (t j a) = None" 
                  unfolding ts' using lts' a ij by auto
                from ij have ij: "i < k" "j < k" using lts' by auto
                have conf: "conflicts (ts ! i) (ts ! j) = None" 
                  unfolding ts_t using ij conf a by (force simp: conflicts.simps set_zip)
                with ts_no_conflict[OF ij] show False ..
              qed
            qed
          } note no_clashes = this

          have True_id: "(True \<and> b \<and> True) = b" for b by simp
          have if_id: "(if xl = [] then Ball P wf_ts2 else Ball P wf_ts)
            = Ball P (\<lambda> ts. if xl = [] then wf_ts2 ts else wf_ts ts)" for P by auto

          (* well-formedness is preserved *)
          have wf': "wf_lr2 (xl, (frrx @ rx2) @ out, b)"
            unfolding wf_lr2_def split wf_rx2_def wf_rx_def snd_conv fst_conv 
            unfolding dist_new b_correct True_id if_id
          proof (intro conjI wflx ballI)
            fix ts'
            assume "ts' \<in> snd ` set ((frrx @ rx2) @ out)" 
            then obtain y where "(y,ts') \<in> set frrx \<or> ts' \<in> snd ` set (rx2 @ out)" by force
            thus "if xl = [] then wf_ts2 ts' else wf_ts ts'" 
            proof
              assume "ts' \<in> snd ` set (rx2 @ out)" 
              with wf show ?thesis unfolding wf_lr2_def split rx wf_rx2_def wf_rx_def
                by auto
            next
              assume "(y,ts') \<in> set frrx" 
              from this[unfolded frrx_def] 
              have tl: "tl ts' \<noteq> []" and in_rrx: "(y,ts') \<in> set rrx" by auto
              from in_rrx[unfolded rrx_def] obtain ts'' where 
                in_rx1: "(y,ts'') \<in> set rx1" and
                rd: "ts' = remdups ts''" by auto
              from in_rx1[unfolded rx1] have "length ts'' = length ts" unfolding k_def by auto
              with ts have ts'': "ts'' \<noteq> []" by auto
              with rd have ts': "ts' \<noteq> []" by auto
              with tl have len2: "length ts' \<ge> 2" by (cases ts'; cases "tl ts'", auto)
              from rd have dist: "distinct ts'" by auto
              {
                fix j i
                assume "j<length ts'" "i<j" 
                hence "ts' ! i \<in> set ts'" "ts' ! j \<in> set ts'" by auto
                hence *: "ts' ! i \<in> set ts''" "ts' ! j \<in> set ts''" unfolding rd by auto
                have "conflicts (ts' ! i) (ts' ! j) \<noteq> None" 
                  by (rule no_clashes[OF _ *, of y], insert in_rx1, auto)
              }
              thus ?thesis unfolding wf_ts2_def wf_ts_def  using ts' len2 dist by auto
            qed
          qed

          (* obtain IH and apply it *)
          note IH = IH[OF measure res wf' lvar_cond_new cond3[rule_format]]

          show ?thesis 
          proof (intro conjI)
            show "wf_lr3 (xl, rx', b)" using IH by auto
            show "lvar_cond_mp n' (mp_lr (xl, rx', b))" using IH by auto
            show "n \<le> n'" using IH by auto
            (* now we only need to perform the steps of the post-processing *)
            (* remdups = many match-duplicate steps *)
            have "mp_lr (xl, rx @ out, b) \<rightarrow>\<^sub>m mp_lr (xl, (rx1 @ rx2) @ out, b)" by fact
            also have "(\<rightarrow>\<^sub>m)\<^sup>*\<^sup>* (mp_lr (xl, (rx1 @ rx2) @ out, b)) (mp_lr (xl, (rrx @ rx2) @ out, b))" 
            proof (rule many_remdups_steps[OF glob_rrx_set_eq[symmetric]])
              have "mp_rx (rrx, b) \<subseteq># mp_rx (rx1, b)" 
                unfolding rrx_def mp_rx_def fst_conv 
              proof (induct rx1)
                case (Cons pair rx2)
                obtain x ts where pair: "pair = (x,ts)" by force
                show ?case unfolding  List.maps_simps list.simps pair split mset_append 
                proof (rule subset_mset.add_mono[OF _ Cons]) 
                  show "mp_list (map (\<lambda>t. (t, Var x)) (remdups ts)) \<subseteq># mp_list (map (\<lambda>t. (t, Var x)) ts)" 
                    unfolding mset_map
                    by (intro image_mset_subseteq_mono mset_remdups_subset_eq)
                qed
              qed auto
              thus "mp_lr (xl, (rrx @ rx2) @ out, b) \<subseteq># mp_lr (xl, (rx1 @ rx2) @ out, b)" 
                unfolding mp_lr_def split mp_rx_append by auto
            qed
            (* filter on length 1 = many match-match steps *)
            also have "(\<rightarrow>\<^sub>m)\<^sup>*\<^sup>* (mp_lr (xl, (rrx @ rx2) @ out, b)) (mp_lr (xl, (frrx @ rx2) @ out, b))" 
            proof -
              define long :: "('v \<times> ('f, nat \<times> 's) Term.term list) \<Rightarrow> bool" where 
                "long =  (\<lambda>(y, ts'). tl ts' \<noteq> [])" 
              define short where "short = Not o long" 
              have short_long: "mp_rx (rrx,b) = mp_rx (filter short rrx,b) + mp_rx (filter long rrx,b)" 
                unfolding mp_rx_def fst_conv short_def by (induct rrx, auto)
              hence expand: "mp_lr (xl, (rrx @ rx2) @ out, b) = 
                mp_rx (filter short rrx, b) + mp_lr (xl, (frrx @ rx2) @ out, b)" 
                unfolding mp_lr_def split mp_rx_append short_long long_def frrx_def by simp
              show ?thesis unfolding expand
              proof (rule many_match_steps)
                fix s lhs 
                assume "(s, lhs) \<in># mp_rx (filter short rrx, b)" 
                from this[unfolded mp_rx_def fst_conv short_def long_def List.maps_def, simplified]
                obtain y ts' where in_rrx: "(y, ts') \<in> set rrx" and lhs: "lhs = Var y" 
                  and "tl ts' = []" "s \<in> set ts'" 
                  by auto
                then have ts': "ts' = [s]" by (cases ts'; cases "tl ts'"; auto)                
                show "\<exists>x. lhs = Var x \<and> x \<notin> lvars_mp
                     (mp_rx (filter short rrx, b) - {#(s, lhs)#} + mp_lr (xl, (frrx @ rx2) @ out, b))" 
                proof (intro exI[of _ y] conjI lhs notI)
                  assume mem: "y \<in> lvars_mp (mp_rx (filter short rrx, b) - {#(s, lhs)#} + mp_lr (xl, (frrx @ rx2) @ out, b))"
                  from in_rrx obtain a 
                    where a: "a < l" and y: "y = fresh ! a" and yts': "(y,ts') = rrx ! a" 
                      unfolding rrx_def rx1 by auto
                  with lfresh have yfresh: "y \<in> set fresh" by auto
                  with lvars_fresh_disj mem
                  have "y \<in> lvars_mp (mp_rx (filter short rrx, b) - {#(s, lhs)#}) \<or> y \<in> lvars_mp (mp_rx (frrx, b))" 
                    unfolding rx mp_lr_def split mp_rx_append mp_rx_Cons lvars_mp_def by auto
                  hence "\<exists> b. b < l \<and> y = fresh ! b \<and> a \<noteq> b"
                  proof
                    assume "y \<in> lvars_mp (mp_rx (frrx, b))" 
                    from this[unfolded frrx_def, folded long_def, unfolded mp_rx_def lvars_mp_def, simplified]
                    obtain ts'' where ts'': "(y, ts'') \<in> set rrx" and long: "long (y, ts'')" by auto 
                    from long ts' have diff: "ts' \<noteq> ts''" unfolding long_def by auto
                    from ts'' obtain b where b: "b < l" and yts'': "(y, ts'') = rrx ! b" and y: "y = fresh ! b" 
                      unfolding rrx_def rx1 by auto
                    from yts' yts'' diff have diff: "a \<noteq> b"
                      by (metis snd_conv)
                    with a b y show ?thesis by auto
                  next
                    assume mem: "y \<in> lvars_mp (mp_rx (filter short rrx, b) - {#(s, lhs)#})"
                    define other where "other = take a rrx @ drop (Suc a) rrx" 
                    have lenrrx: "length rrx = l" unfolding rrx_def rx1 by auto
                    hence "rrx = take a rrx @ rrx ! a # drop (Suc a) rrx" using a 
                      by (meson id_take_nth_drop)
                    hence "filter short rrx = filter short (take a rrx @ rrx ! a # drop (Suc a) rrx)" by simp
                    also have "\<dots> = filter short (take a rrx) @ rrx ! a # filter short (drop (Suc a) rrx)" 
                      (is "_ = ?f1 @ _ # ?f2")
                      by (simp add: yts'[symmetric] short_def long_def ts')
                    also have "rrx ! a = (y, [s])" unfolding yts'[symmetric] ts' by simp
                    also have "mp_rx (?f1 @ \<dots> # ?f2, b) - {#(s,lhs)#} = mp_rx (?f1 @ ?f2,b)" 
                      unfolding mp_rx_append mp_rx_Cons lhs split by auto
                    finally have "y \<in> lvars_mp (mp_rx (?f1 @ ?f2,b))" using mem by auto
                    from this[unfolded lvars_mp_def mp_rx_def, folded filter_append, folded other_def]
                    obtain ts'' where "(y,ts'') \<in> set other" by auto
                    also have "\<dots> \<subseteq> {rrx ! b | b. b \<in> {..<length rrx} - {a}}" unfolding other_def
                      using a unfolding lenrrx[symmetric] unfolding set_conv_nth
                      by (auto simp: nth_append) 
                        (metis (no_types, lifting) Suc_diff_diff diff_self_eq_0 diff_zero lessI less_nat_zero_code neq0_conv
                          zero_less_diff)
                    finally obtain b where "b < l" "a \<noteq> b" and "(y, ts'') = rrx ! b" using lenrrx by auto
                    then show ?thesis using lenrrx unfolding rrx_def rx1 by auto
                  qed
                  then obtain b where "b < l" "y = fresh ! b" "a \<noteq> b" by auto
                  with y a show False using injD[OF ren(1), of "n + a" "n + b"] unfolding fresh_def 
                    by auto
                qed
              qed
            qed
            also have "(\<rightarrow>\<^sub>m)\<^sup>*\<^sup>* (mp_lr (xl, (frrx @ rx2) @ out, b)) (mp_lr (xl, rx', b))" using IH by auto
            finally show "(\<rightarrow>\<^sub>m)\<^sup>*\<^sup>* (mp_lr (xl, rx @ out, b)) (mp_lr (xl, rx', b))" .
          qed
        qed
      qed
    qed
  } note main = this
  from assms(4)[unfolded decomp'_impl_def mp split]
  obtain rx' where decomp: "Decomp'_main_loop n xs rx [] = (n', rx')" (is "?e = _")
    and mp': "mp' = (xl, rx', b)" by (cases ?e, auto)
  from main[OF decomp, unfolded append_Nil2, folded mp mp'] 1
  show ?case using assms by auto
qed

lemma match_decomp'_impl: assumes "Match_decomp'_impl n mp = res" 
  and lvc: "lvar_cond_mp n (mp_list mp)" 
  shows "res = Some (n',mp') \<Longrightarrow> (\<rightarrow>\<^sub>m)\<^sup>*\<^sup>* (mp_list mp) (mp_lr mp') \<and> wf_lr3 mp' \<and> lvar_cond_mp n' (mp_lr mp') \<and> n \<le> n'" 
    and "res = None \<Longrightarrow> \<exists> mp'. (\<rightarrow>\<^sub>m)\<^sup>*\<^sup>* (mp_list mp) mp' \<and> match_fail mp'" 
proof (atomize (full), goal_cases)
  case 1
  note res = assms(1)[unfolded match_decomp'_impl_def]
  show ?case
  proof (cases "match_steps_impl mp = None")
    case None: True
    with match_steps_impl(2)[OF refl None] 
    show ?thesis using res by auto
  next
    case False
    then obtain xs mp2 where Some: "match_steps_impl mp = Some (xs, mp2)" by auto
    note match = match_steps_impl(1)[OF refl Some]
    from lvc match have lvc: "lvar_cond_mp n (mp_lr mp2)" 
      unfolding lvar_cond_def lvar_cond_mp_def by auto
    note res = res[unfolded Some option.simps split]
    show ?thesis 
    proof (cases "apply_decompose' mp2")
      case False
      obtain xl xr b where mp2: "mp2 = (xl,xr,b)" by (cases mp2, auto)
      from False[unfolded apply_decompose'_def mp2 split] 
      have cond: "improved \<Longrightarrow> b \<or> xl \<noteq> []" by auto
      from match have "wf_lr2 mp2" by simp
      with cond have "wf_lr3 mp2" 
        unfolding wf_lr3_def wf_lr2_def mp2 split
        unfolding wf_rx3_def by auto
      with False res lvc match show ?thesis by auto
    next
      case True
      with res have res: "res = Some (decomp'_impl renNat n xs mp2)" by auto
      obtain n3 mp3 where dec: "decomp'_impl renNat n xs mp2 = (n3, mp3)" (is "?e = _") by (cases ?e) auto
      from True have improved unfolding apply_decompose'_def by (cases mp2, auto)
      from match 
      have steps12: "(\<rightarrow>\<^sub>m)\<^sup>*\<^sup>* (mp_list mp) (mp_lr mp2)" 
        and wf2: "wf_lr2 mp2" 
        and xs: "set xs = lvars_mp (mp_list (mp_lx (fst mp2)))" by auto
      from decomp'_impl[OF wf2 xs lvc dec \<open>improved\<close>] steps12
      show ?thesis unfolding res dec by auto
    qed
  qed
qed

lemma pat_inner_impl: assumes "Pat_inner_impl n p pd = res" 
  and "wf_pat_lr pd" 
  and "tvars_pat (pat_mset (pat_mset_list p + pat_lr pd)) \<subseteq> V" 
  and "lvar_cond_pp n (pat_mset_list p + pat_lr pd)" 
  shows "res = None \<Longrightarrow> (add_mset (pat_mset_list p + pat_lr pd) P, P) \<in> \<Rrightarrow>\<^sup>+" 
    and "res = Some (n',p') \<Longrightarrow> (add_mset (pat_mset_list p + pat_lr pd) P, add_mset (pat_lr p') P) \<in> \<Rrightarrow>\<^sup>*
             \<and> wf_pat_lr p' \<and> tvars_pat (pat_mset (pat_lr p')) \<subseteq> V \<and> lvar_cond_pp n' (pat_lr p') \<and> n \<le> n'" 
proof (atomize(full), insert assms, induct p arbitrary: n pd res n' p')
  case Nil
  then show ?case by (auto simp: wf_pat_lr_def pat_mset_list_def pat_lr_def)
next
  case (Cons mp p n pd res n'' p')
  let ?p = "pat_mset_list p + pat_lr pd" 
  have id: "pat_mset_list (mp # p) + pat_lr pd = add_mset (mp_list mp) ?p" unfolding pat_mset_list_def by auto  
  from Cons(5) have lmp: "lvar_cond_mp n (mp_list mp)" unfolding lvar_cond_pp_def lvar_cond_mp_def lvars_pp_def
    by (simp add: id)
  show ?case
  proof (cases "Match_decomp'_impl n mp")
    case (Some pair)
    then obtain n' mp' where Some: "Match_decomp'_impl n mp = Some (n', mp')" by (cases pair, auto)
    from match_decomp'_impl(1)[OF Some lmp refl]
    have steps: "(\<rightarrow>\<^sub>m)\<^sup>*\<^sup>* (mp_list mp) (mp_lr mp')" and wf: "wf_lr3 mp'" 
      and lmp': "lvar_cond_mp n' (mp_lr mp')" and nn': "n \<le> n'" by auto
    from Cons(5) lvar_cond_mono[OF nn'] 
    have lvars_n': "lvar_cond_pp n' (pat_mset_list (mp # p) + pat_lr pd)" 
      by (auto simp: lvar_cond_pp_def)
    have id2: "pat_mset_list p + pat_lr (mp' # pd) = add_mset (mp_lr mp') ?p" unfolding pat_lr_def by auto
    from mp_step_mset_steps_vars[OF steps] Cons(4) 
    have vars: "tvars_pat (pat_mset (pat_mset_list p + pat_lr (mp' # pd))) \<subseteq> V"
        unfolding id2 by (auto simp: tvars_pat_def pat_mset_list_def)
    note steps = mp_step_mset_cong[OF steps, of ?p P, folded id]
    note res = Cons(2)[unfolded pat_inner_impl.simps Some option.simps split]
    show ?thesis 
    proof (cases "empty_lr mp'")
      case False
      with Cons(3) wf have wf: "wf_pat_lr (mp' # pd)" unfolding wf_pat_lr_def by auto
      from lmp' lvars_n' 
      have lvars_pre: "lvar_cond_pp n' (pat_mset_list p + pat_lr (mp' # pd))" 
        unfolding lvar_cond_pp_def lvar_cond_mp_def 
        by (auto simp: pat_mset_list_def lvars_pp_def lvars_mp_def pat_lr_def) 
      from res False have "Pat_inner_impl n' p (mp' # pd) = res" by auto
      from Cons(1)[OF this wf vars lvars_pre, of n'' p', unfolded id2] steps nn'
      show ?thesis by auto
    next
      case True
      with wf have id3: "mp_lr mp' = {#}" unfolding wf_lr2_def empty_lr_def by (cases mp', auto simp: mp_lr_def mp_rx_def List.maps_def)
      from True res have res: "res = None" by auto
      have "(add_mset (add_mset (mp_lr mp') ?p) P, P) \<in> P_step" 
        unfolding id3 P_step_def using P_simp_pp[OF pat_remove_pp[of ?p], of P] by auto
      with res steps show ?thesis by auto
    qed
  next
    case None
    from match_decomp'_impl(2)[OF None lmp refl] obtain mp' where
      "(\<rightarrow>\<^sub>m)\<^sup>*\<^sup>* (mp_list mp) mp'" and fail: "match_fail mp'" by auto
    note steps = mp_step_mset_cong[OF this(1), of ?p P, folded id]
    from P_simp_pp[OF pat_remove_mp[OF fail, of ?p], of P]
    have "(add_mset (add_mset mp' ?p) P, add_mset ?p P) \<in> P_step" 
      unfolding P_step_def by auto
    with steps have steps: "(add_mset (pat_mset_list (mp # p) + pat_lr pd) P, add_mset ?p P) \<in> P_step^*" by auto
    note res = Cons(2)[unfolded pat_inner_impl.simps None option.simps] 
    have vars: "tvars_pat (pat_mset (pat_mset_list p + pat_lr pd)) \<subseteq> V" 
      using Cons(4) unfolding tvars_pat_def pat_mset_list_def by auto
    have lvars: "lvar_cond_pp n (pat_mset_list p + pat_lr pd)" 
      using Cons(5) unfolding lvar_cond_pp_def lvars_pp_def by (auto simp: pat_mset_list_def)
    from Cons(1)[OF res Cons(3) vars lvars, of n'' p'] steps 
    show ?thesis by auto
  qed
qed

text \<open>Main simulation lemma for a single @{const pat_impl} step.\<close>
lemma pat_impl:
  assumes "Pat_impl n nl p = res" 
    and vars: "tvars_pat (pat_list p) \<subseteq> {..<n} \<times> S"
    and lvarsAll: "\<forall> pp \<in># add_mset (pat_mset_list p) P. lvar_cond_pp nl pp"  
  shows "res = Incomplete \<Longrightarrow> \<exists> p'. (add_mset (pat_mset_list p) P, add_mset p' P) \<in> \<Rrightarrow>\<^sup>* \<and> pat_fail p'" 
    and "res = New_Problems (n',nl',ps) \<Longrightarrow> (add_mset (pat_mset_list p) P, mset (map pat_mset_list ps) + P) \<in> \<Rrightarrow>\<^sup>+
             \<and> tvars_pat (\<Union> (pat_list ` set ps)) \<subseteq> {..< n'} \<times> S
             \<and> (\<forall> pp \<in># mset (map pat_mset_list ps) + P. lvar_cond_pp nl' pp) \<and> n \<le> n'" 
    and "res = Fin_Var_Form fvf \<Longrightarrow> improved 
             \<and> (add_mset (pat_mset_list p) P, add_mset (pat_mset_list (pat_of_var_form_list fvf)) P) \<in> \<Rrightarrow>\<^sup>* 
             \<and> finite_var_form_pat C (pat_list (pat_of_var_form_list fvf))
             \<and> Ball (set fvf) (distinct o map fst)
             \<and> Ball (set (concat fvf)) (distinct \<circ> snd)" 
proof (atomize(full), goal_cases)
  case 1
  have wf: "wf_pat_lr []" unfolding wf_pat_lr_def by auto
  have vars: "tvars_pat (pat_mset (pat_mset_list p)) \<subseteq> {..<n} \<times> S"
    using vars unfolding pat_mset_list by auto
  have "pat_mset_list p + pat_lr [] = pat_mset_list p" unfolding pat_lr_def by auto
  note pat_inner = pat_inner_impl[OF refl wf, of p, unfolded this, OF vars]
  from lvarsAll have lvars: "lvar_cond_pp nl (pat_mset_list p)" by auto
  note res = assms(1)[unfolded pat_impl_def]
  show ?case
  proof (cases "Pat_inner_impl nl p []")
    case None
    from pat_inner(1)[OF lvars this] res[unfolded None option.simps] vars
    show ?thesis using lvarsAll by (auto simp: tvars_pat_def)
  next
    case (Some pair)
    then obtain nl'' p' where Some: "Pat_inner_impl nl p [] = Some (nl'', p')" by force
    from pat_inner(2)[OF lvars Some]
    have steps: "(add_mset (pat_mset_list p) P, add_mset (pat_lr p') P) \<in> \<Rrightarrow>\<^sup>*"
      and wf: "wf_pat_lr p'"
      and varsp': "tvars_pat (pat_mset (pat_lr p')) \<subseteq> {..<n} \<times> S"
      and lvar_p': "lvar_cond_pp nl'' (pat_lr p')" and nl: "nl \<le> nl''" by auto
    obtain ivc no_ivc where part: "partition (\<lambda>mp. snd (snd mp)) p' = (ivc, no_ivc)" by force
    from part have no_ivc_filter: "no_ivc = filter (\<lambda> mp. \<not> (snd (snd mp))) p'" unfolding partition_filter_conv
      by (auto simp: o_def)
    from part have ivc_filter: "ivc = filter (\<lambda> mp. snd (snd mp)) p'" unfolding partition_filter_conv
      by (auto simp: o_def)
    define f where "f = (\<lambda> mp :: ('f,'v,'s)match_problem_lr. snd (snd mp))" 
    from part have Notf: "no_ivc = filter (Not o f) p'" unfolding partition_filter_conv f_def
      by (auto simp: o_def)
    from part have f: "ivc = filter f p'" unfolding partition_filter_conv f_def
      by (auto simp: o_def)
    note res = res[unfolded Some option.simps split part]
    show ?thesis
    proof (cases "\<forall>mp\<in>set p'. snd (snd mp)")
      case True
      with res part have res: "res = Incomplete" by auto
      have "(add_mset (pat_lr p') P, add_mset {#} P) \<in> \<Rrightarrow>\<^sup>*" 
      proof (cases "pat_lr p' = {#}")
        case False
        have "add_mset (pat_lr p' + {#}) P \<Rrightarrow>\<^sub>m {# {#} #} + P" 
        proof (intro P_simp_pp[OF pat_inf_var_conflict[OF _ False]] ballI)
          fix mps
          assume "mps \<in> pat_mset (pat_lr p')" 
          then obtain mp where mem: "mp \<in> set p'" and mps: "mps = mp_mset (mp_lr mp)" by (auto simp: pat_lr_def)
          obtain lx rx b where mp: "mp = (lx,rx,b)" by (cases mp, auto)
          from mp mem True have b by auto
          with wf[unfolded wf_pat_lr_def, rule_format, OF mem, unfolded wf_lr3_def mp split]
          have "inf_var_conflict (set_mset (mp_rx (rx,b)))" unfolding wf_rx_def wf_rx2_def wf_rx3_def by (auto split: if_splits)
          thus "inf_var_conflict mps" unfolding mps mp_lr_def mp split
            unfolding inf_var_conflict_def by fastforce
        qed (auto simp: tvars_pat_def)
        thus ?thesis unfolding P_step_def by auto
      qed auto
      with steps have "(add_mset (pat_mset_list p) P, add_mset {#} P) \<in> \<Rrightarrow>\<^sup>*" by auto
      moreover have "pat_fail {#}" by (intro pat_empty)
      ultimately show ?thesis using res by auto 
    next
      case False
      with part have no_ivc: "no_ivc \<noteq> []" unfolding partition_filter_conv o_def
        by (metis (no_types, lifting) empty_filter_conv snd_conv)
      hence "(no_ivc = []) = False" by auto
      note res = res[unfolded this if_False]
      from part have sub: "set no_ivc \<subseteq> set p'" "set ivc \<subseteq> set p'" unfolding partition_filter_conv by auto
      {
        fix mp
        assume mp: "mp \<in> set no_ivc" 
        with no_ivc_filter have b: "\<not> snd (snd mp)" by simp
        from mp sub have "mp \<in> set p'" by auto
        with wf[unfolded wf_pat_lr_def] have "wf_lr3 mp" by auto
        from this[unfolded wf_lr3_def wf_rx3_def wf_rx_def wf_rx2_def] b
        have "\<not> inf_var_conflict (mp_mset (mp_rx (snd mp)))" 
          by (cases mp, auto split: if_splits)
        note b this
      } note no_ivc_b = this

      {
        fix mp
        assume mp: "mp \<in> set ivc" 
        with ivc_filter have b: "snd (snd mp)" by simp
        from mp sub have "mp \<in> set p'" by auto
        with wf[unfolded wf_pat_lr_def] have "wf_lr3 mp" by auto
        from this[unfolded wf_lr3_def wf_rx3_def wf_rx_def wf_rx2_def] b
        have "inf_var_conflict (mp_mset (mp_rx (snd mp)))" 
          by (cases mp, auto split: if_splits)
        note b this
      } note ivc_b = this

      define p'l where "p'l = map mp_lr_list p'" 
      let ?ivc'_cond = "improved \<and> ivc \<noteq> [] \<and> (\<forall>mp\<in>set no_ivc. fst mp = [])" 
      show ?thesis
      proof (cases ?ivc'_cond)
        case True  
        hence "?ivc'_cond = True" by auto
        note res = res[unfolded this if_True, symmetric]
        from True CC have "CC = C" by auto
        note res = res[unfolded this]
        define M where "M = pat_lr ivc" 
        let ?f = "(\<lambda>mp. \<forall>xts\<in>set (fst (snd mp)). is_singleton_list (map \<T>(C,\<V>) (snd xts)))" 
        define P' where "P' = filter ?f no_ivc" 
        have P': "set P' \<subseteq> set p'" unfolding P'_def no_ivc_filter by auto
        have p'_split: "pat_lr p' = M + pat_lr no_ivc" 
          unfolding pat_lr_def ivc_filter no_ivc_filter mset_map M_def
          by (induct p', auto)
        from no_ivc_filter have "set no_ivc \<subseteq> set p'" by auto
        hence steps2: "(add_mset (M + pat_lr no_ivc) P, add_mset (M + pat_lr P') P) \<in> \<Rrightarrow>\<^sup>*" unfolding P'_def
        proof (induct no_ivc arbitrary: M)
          case (Cons mp mps M)       
          show ?case
          proof (cases "?f mp")
            case True
            have "add_mset (M + pat_lr  (mp # mps)) P = add_mset ((M + pat_lr [mp]) + pat_lr mps) P" 
              unfolding pat_lr_def by auto
            also have "(\<dots>, add_mset ((M + pat_lr [mp]) + pat_lr (filter ?f mps)) P) \<in> \<Rrightarrow>\<^sup>*" 
              by (rule Cons(1), insert Cons, auto)
            also have "(M + pat_lr [mp]) + pat_lr (filter ?f mps) = M + pat_lr (filter ?f (mp # mps))" 
              unfolding pat_lr_def using True by auto
            finally show ?thesis .
          next
            case False
            have "add_mset (M + pat_lr  (mp # mps)) P = add_mset (add_mset (mp_lr mp) (M + pat_lr mps)) P"
              unfolding pat_lr_def by simp
            also have "(\<dots>, {#  M + pat_lr mps #} + P) \<in> \<Rrightarrow>" unfolding P_step_def
            proof (standard, unfold split, rule P_simp_pp, rule pat_remove_mp)
              obtain xl xr b where mp: "mp = (xl,xr,b)" by (cases mp, auto)
              with Cons(2) have mem: "(xl,xr,b) \<in> set p'" by auto
              from mp False obtain x ts where xts: "(x,ts) \<in> set xr" 
                 and nsingle: "\<not> is_singleton_list (map \<T>(C,\<V>) ts)" by auto
              from wf[unfolded wf_pat_lr_def, rule_format, OF mem]
              have "wf_lr3 (xl,xr,b)" by auto
              from this[unfolded wf_lr3_def split] have "wf_rx3 (xr,b) \<or> wf_rx (xr,b)" by (auto split: if_splits)
              with xts have "wf_ts2 ts \<or> wf_ts ts" unfolding wf_rx3_def wf_rx2_def wf_rx_def
                by auto
              hence "ts \<noteq> []" unfolding wf_ts2_def wf_ts_def by auto
              then obtain t ts' where ts: "ts = t # ts'" by (cases ts, auto)
              from nsingle[unfolded is_singleton_list ts singleton_def]
              obtain t' where t': "t' \<in> set ts'" and diff: "\<T>(C,\<V>) t \<noteq> \<T>(C,\<V>) t'" by force
              from split_list[OF t'] obtain bef aft where ts': "ts' = bef @ t' # aft" by auto
              from split_list[OF xts] obtain bef' aft' where xr: "xr = bef' @ (x, ts) # aft'" by auto
              obtain M' where mp: "mp_lr mp = add_mset (t,Var x) (add_mset (t', Var x) M')" 
                unfolding mp ts ts' xr
                unfolding mp_lr_def by (auto simp: mp_rx_def List.maps_def)
              show "match_fail (mp_lr mp)" unfolding mp
                by (rule match_clash_sort[OF diff])
            qed
            also have "{#  M + pat_lr mps #} + P = add_mset (M + pat_lr mps) P" by auto
            also have "(\<dots>, add_mset (M + pat_lr (filter ?f mps)) P) \<in> \<Rrightarrow>\<^sup>*" 
              by (rule Cons(1), insert Cons, auto)
            also have "M + pat_lr (filter ?f mps) = M + pat_lr (filter ?f (mp # mps))" 
              using False by auto
            finally show ?thesis .
          qed
        qed auto
        from steps[unfolded p'_split] steps2 
        have steps: "(add_mset (pat_mset_list p) P, add_mset (M + pat_lr P') P) \<in> \<Rrightarrow>\<^sup>*" by auto
        have step: "(add_mset (M + pat_lr P') P, {# pat_lr P' #} + P) \<in> \<Rrightarrow>" 
          unfolding P_step_def
        proof (standard, unfold split, rule P_simp_pp, rule pat_inf_var_conflict)
          from True have "ivc \<noteq> []" by auto
          then obtain lx rx b ivc' where ivc: "ivc = (lx,rx,b) # ivc'" by (cases ivc, auto)
          hence "(lx,rx,b) \<in> set ivc" by auto
          from ivc_b[OF this] have "mp_rx (rx,b) \<noteq> {#}" unfolding inf_var_conflict_def by auto
          thus "M \<noteq> {#}" unfolding M_def ivc pat_lr_def by auto
        next
          {
            fix xl xr b
            assume "(xl, xr, b) \<in> set ivc" 
            from ivc_b[OF this] have "inf_var_conflict (mp_mset (mp_rx ((xr, b))))" by simp
            hence "inf_var_conflict (mp_mset (mp_lr (xl, xr, b)))" 
              unfolding mp_lr_def inf_var_conflict_def by force
          }
          thus "Ball (pat_mset M) inf_var_conflict" unfolding M_def pat_lr_def by auto
        next
          show "\<forall>x\<in>tvars_pat (pat_mset (pat_lr P')). \<not> inf_sort (snd x)" 
          proof
            fix y
            assume "y \<in> tvars_pat (pat_mset (pat_lr P'))" 
            from this[unfolded tvars_pat_def pat_lr_def, simplified] obtain mp
              where mp: "mp \<in> set P'" and y: "y \<in> tvars_match (mp_mset (mp_lr mp))"
              by auto
            from wf[unfolded wf_pat_lr_def] P' mp have wf: "wf_lr3 mp" by auto
            from mp[unfolded P'_def] have mp: "mp \<in> set no_ivc" and fmp: "?f mp" by auto
            from no_ivc_b[OF mp] True mp
            obtain rx where mp_id: "mp = ([],rx,False)" 
              and ninf: "\<not> inf_var_conflict (mp_mset (mp_rx (rx, False)))" 
              by (cases mp, auto)  
            note fmp = fmp[unfolded mp_id snd_conv fst_conv]
            have id: "mp_lr mp = mp_rx (rx,False)" unfolding mp_id mp_lr_def by auto
            from y[unfolded id mp_rx_def List.maps_def tvars_match_def]
            obtain x ts t where xts: "(x,ts) \<in> set rx" and t: "t \<in> set ts" and y: "y \<in> vars t" by force
            from wf[unfolded mp_id wf_lr3_def split] 
            have "wf_rx3 (rx, False)" by auto
            from this[unfolded wf_rx3_def] xts True 
            have "wf_ts3 ts" and wf2: "wf_rx2 (rx, False)" by auto
            from this[unfolded wf_ts3_def] obtain z where z: "Var z \<in> set ts" by auto
            have sort: "\<T>(C,\<V>) (Var z) = Some (snd z)" by simp
            from fmp[rule_format, OF xts] 
            have "is_singleton_list (map \<T>(C,\<V>) ts)" by auto 
            from this[unfolded is_singleton_list singleton_def] obtain so 
              where "set (map \<T>(C,\<V>) ts) = {so}" by auto
            with z sort 
            have single: "set (map \<T>(C,\<V>) ts) = {Some (snd z)}" by force
            from wf2[unfolded wf_rx2_def fst_conv] xts 
            have wf2: "wf_ts2 ts" by auto
            from this[unfolded wf_ts2_def] z obtain s where s: "s \<in> set ts" and sz: "s \<noteq> Var z" 
              by (cases ts; cases "tl ts", auto)
            from wf2[unfolded wf_ts2_def wf_ts_no_conflict_alt_def] 
            have no_conf: "s \<in> set ts \<Longrightarrow> t \<in> set ts \<Longrightarrow> conflicts s t \<noteq> None" for s t by auto
            from s z xts have 
              mem: "(Var z, Var x) \<in> mp_mset (mp_rx (rx, False))" 
              "(s, Var x) \<in> mp_mset (mp_rx (rx, False))" 
              unfolding mp_rx_def List.maps_def by auto
            from no_conf[OF z s]
            have "Conflict_Var (Var z) s z" using sz by (cases s, auto simp: conflicts.simps)
            with ninf mem have ninf :"\<not> inf_sort (snd z)" 
              unfolding inf_var_conflict_def by blast
            define \<sigma> where "\<sigma> = snd z" 
            from single t 
            have t: "t : \<sigma> in \<T>(C,\<V>)" unfolding hastype_def \<sigma>_def by auto
            from t y ninf[folded \<sigma>_def]
            show "\<not> inf_sort (snd y)" 
              by (rule finite_sort_imp_finite_sort_vars)
          qed
        qed (insert True, auto)
        have "{# pat_lr P' #} + P = add_mset (pat_lr P') P" by simp  
        also have to_list: "pat_lr P' = pat_mset_list (map mp_lr_list P')" by (simp add: pat_mset_list_lr)
        finally have steps: "(add_mset (pat_mset_list p) P, add_mset (pat_mset_list (map mp_lr_list P')) P) \<in> \<Rrightarrow>\<^sup>+" 
          using steps step by (simp add: pat_mset_list_lr)        
        show ?thesis
        proof (intro conjI impI)
          assume "res = New_Problems (n', nl', ps)" 
          from res[unfolded this]
          have id: "n' = n" "nl' = nl''" "ps = [map mp_lr_list P']" 
            by (auto simp: P'_def)
          show "(add_mset (pat_mset_list p) P, mset (map pat_mset_list ps) + P) \<in> \<Rrightarrow>\<^sup>+" 
            unfolding id using steps by auto
          show "n \<le> n'" unfolding id by auto
          have "tvars_pat (\<Union> (pat_list ` set ps)) \<subseteq> tvars_pat (pat_list (map mp_lr_list P'))" 
            unfolding id by auto
          also have id2: "pat_list (map mp_lr_list P') = pat_mset (pat_lr P')" unfolding to_list
            by (metis pat_mset_list)
          also have "tvars_pat \<dots> \<subseteq> tvars_pat (pat_mset (pat_lr p'))" using P' 
            unfolding tvars_pat_def pat_lr_def by force
          also have "\<dots> \<subseteq> {..<n} \<times> S" by fact
          finally show "tvars_pat (\<Union> (pat_list ` set ps)) \<subseteq> {..<n'} \<times> S" 
            unfolding id .
          show "Multiset.Ball (mset (map pat_mset_list ps) + P) (lvar_cond_pp nl')" 
          proof
            fix mps
            assume "mps \<in># mset (map pat_mset_list ps) + P" 
            from this[unfolded id] 
            have disj: "mps = pat_mset_list (map mp_lr_list P') \<or> mps \<in># P" by auto
            thus "lvar_cond_pp nl' mps" 
            proof 
              assume "mps \<in># P" 
              with lvarsAll have "lvar_cond_pp nl mps" by auto
              with lvar_cond_mono[OF nl] show "lvar_cond_pp nl' mps" 
                unfolding lvar_cond_pp_def id by auto
            next
              assume "mps = pat_mset_list (map mp_lr_list P')" 
              also have "\<dots> = pat_lr P'" by (rule pat_mset_list_lr)
              also have "\<dots> \<subseteq># pat_lr no_ivc" unfolding P'_def pat_lr_def mset_map mset_filter
                by (rule image_mset_subseteq_mono, rule multiset_filter_subset)
              also have "\<dots> \<subseteq># pat_lr p'" unfolding p'_split by auto
              finally have "lvars_pp mps \<subseteq> lvars_pp (pat_lr p')" 
                unfolding lvars_pp_def using mset_subset_eqD by fastforce
              with lvar_p' show ?thesis unfolding id lvar_cond_pp_def lvar_cond_def by auto
            qed
          qed             
        qed (insert res, auto)
      next
        case False
        hence "?ivc'_cond = False" by auto
        note res = res[unfolded this if_False]
        show ?thesis 
        proof (cases "find_var improved no_ivc")
          case (Some x)
          define ps where "ps = map (\<lambda>\<tau>. subst_pat_problem_list \<tau> p'l) (\<tau>s_list n x)"
          have id: "pat_lr p' = pat_mset_list p'l" unfolding p'l_def by (simp add: pat_mset_list_lr)
          have subst: "map (\<lambda>\<tau>. subst_pat_problem_mset \<tau> (pat_lr p')) (\<tau>s_list n x) = map pat_mset_list ps"
            unfolding id
            unfolding ps_def subst_pat_problem_list_def subst_pat_problem_mset_def subst_match_problem_mset_def
              subst_match_problem_list_def map_map o_def
            by (intro list.map_cong0, auto simp: pat_mset_list_def o_def image_mset.compositionality)
          note res = res[unfolded Let_def Some option.simps, folded p'l_def]
          from res have res: "res = New_Problems (n + m, nl'', ps)" using ps_def by auto
          have step: "(add_mset (pat_lr p') P, mset (map pat_mset_list ps) + P) \<in> \<Rrightarrow>"
            unfolding P_step_def
          proof (standard, unfold split, intro P_simp_pp)
            note x = Some[unfolded find_var_def]
            let ?concat = "List.maps (\<lambda> (lx,_). lx) no_ivc" 
            have disj: "tvars_disj_pp {n..<n + m} (pat_mset (pat_lr p'))" 
              using varsp' unfolding tvars_pat_def tvars_disj_pp_def tvars_match_def by force
            show "pat_lr p' \<Rightarrow>\<^sub>m mset (map pat_mset_list ps)" 
            proof (cases ?concat)
              case (Cons pair list)
              with x obtain t where concat: "?concat = (x,t) # list" by (cases pair, auto)
              hence "(x,t) \<in> set ?concat" by auto
              then obtain mp where "mp \<in> set p'" and "(x,t) \<in> set ((\<lambda> (lx,_). lx) mp)" using sub 
                by (auto simp: List.maps_def)
              then obtain lx rx where mem: "(lx,rx) \<in> set p'" and xt: "(x,t) \<in> set lx" by auto
              from wf mem have wf: "wf_lx lx" unfolding wf_pat_lr_def wf_lr3_def by auto
              with xt have t: "is_Fun t" unfolding wf_lx_def by auto
              from mem obtain p'' where pat: "pat_lr p' = add_mset (mp_lr (lx,rx)) p''" 
                unfolding pat_lr_def by simp (metis in_map_mset mset_add set_mset_mset)
              from xt have xt: "(Var x, t) \<in># mp_lr (lx,rx)" unfolding mp_lr_def by force
              from pat_instantiate[OF _ disjI1[OF conjI[OF xt t]], of n p'', folded pat, OF disj]
              show ?thesis unfolding subst .
            next
              case Nil
              define flat_mps where "flat_mps = List.maps (fst \<circ> snd) no_ivc" 
              note x = x[unfolded Nil list.simps Let_def, folded flat_mps_def]  
              from wf[unfolded wf_pat_lr_def]
              show ?thesis
              proof (cases improved)
                case False
                from no_ivc obtain mp p'' where fp: "no_ivc = mp # p''" by (cases no_ivc) auto
                obtain lx rx b where mp: "mp = (lx,rx,b)" by (cases mp) auto
                from fp have hd: "hd no_ivc = mp" by auto
                from no_ivc_b[of mp, unfolded fp] mp 
                have mp: "mp = (lx,rx,False)" by auto
                have mpp: "mp \<in> set p'" using arg_cong[OF fp, of set] sub by auto
                from mp Nil fp have "lx = []" by (auto simp: List.maps_def)
                with mp have mp: "mp = ([],rx,False)" by auto
                note x = x[unfolded hd mp Let_def split]
                from wf mpp have wf: "wf_lr3 mp" and ne: "\<not> empty_lr mp"  unfolding wf_pat_lr_def by auto
                from wf[unfolded wf_lr3_def mp split] mp
                have wf: "wf_rx2 (rx, False)" by (auto simp: wf_rx3_def)
                from ne[unfolded empty_lr_def mp split] obtain y ts rx' 
                  where rx: "rx = (y,ts) # rx'" by (cases rx, auto)
                from wf[unfolded wf_rx2_def] have ninf: "\<not> inf_var_conflict (mp_mset (mp_rx (rx, False)))" 
                  and wf: "wf_ts2 ts" unfolding rx by auto   
                from wf[unfolded wf_ts2_def] obtain s t ts' where ts: "ts = s # t # ts'" and 
                  diff: "s \<noteq> t" and conf: "conflicts s t \<noteq> None" 
                  by (cases ts; cases "tl ts", auto)
                from conf obtain xs where conf: "conflicts s t = Some xs" by (cases "conflicts s t", auto)
                with conflicts(5)[of s t] diff have "xs \<noteq> []" by auto
                with x[unfolded rx list.simps list.sel split ts conf option.sel] False
                obtain xs' where xs: "xs = x # xs'" by (cases xs) auto
                from conf xs have confl: "Conflict_Var s t x" by auto
                from ts rx have sty: "(s, Var y) \<in># mp_rx (rx, False)" "(t, Var y) \<in># mp_rx (rx,False)" 
                  by (auto simp: mp_rx_def List.maps_def)
                with confl ninf have "\<not> inf_sort (snd x)" unfolding inf_var_conflict_def by blast
                with sty confl rx have main: "(s, Var y) \<in># mp_lr mp \<and> (t, Var y) \<in># mp_lr mp \<and> Conflict_Var s t x \<and> \<not> inf_sort (snd x)
            \<and> (improved \<longrightarrow> b)" for b using False
                  unfolding mp by (auto simp: mp_lr_def)
                from mpp obtain p'' where pat: "pat_lr p' = add_mset (mp_lr mp) p''" 
                  unfolding pat_lr_def by simp (metis in_map_mset mset_add set_mset_mset)
                from pat_instantiate[OF _ disjI2[OF main], of n p'', folded pat, OF disj]
                show ?thesis unfolding subst .
              next
                case impr: True
                hence "improved = True" by auto
                note x = x[unfolded this if_True]
                let ?find = "find (\<lambda>rx. \<exists>t\<in>set (snd rx). is_Fun t) flat_mps" 
                from x obtain rx where find: "?find = Some rx" by (cases ?find; force)
                from this[unfolded find_Some_iff]
                obtain t where rx: "rx \<in> set flat_mps" and t: "t \<in> set (snd rx)" "is_Fun t" 
                  by auto
                obtain y ts where rx_id: "rx = (y,ts)" by force  
                note x = x[unfolded find option.simps rx_id split]
                from rx[unfolded flat_mps_def List.maps_def] 
                obtain mp where mp_mem: "mp \<in> set no_ivc" 
                  and rx_mp: "rx \<in> set (fst (snd mp))" by auto
                from mp_mem sub have mp_mem_p': "mp \<in> set p'" by auto
                then obtain p'' where pat: "pat_lr p' = add_mset (mp_lr mp) p''" 
                  unfolding pat_lr_def by simp (metis in_map_mset mset_add set_mset_mset)
                obtain lx rxs b where mp: "mp = (lx,rxs,b)" by (cases mp, auto)
                with rx_mp have rx_rxs: "rx \<in> set rxs" by auto
                from split_list[OF mp_mem] Nil mp
                have lx: "lx = []" unfolding List.maps_def by auto
                from no_ivc_b[OF mp_mem] mp lx
                have mp: "mp = ([],rxs,False)" and 
                  No_ivc: "\<not> inf_var_conflict (mp_mset (mp_rx (rxs,b)))" by auto
                from wf[unfolded wf_pat_lr_def] mp_mem sub 
                have "wf_lr3 mp" by auto
                from this[unfolded wf_lr3_def mp split] 
                have "wf_rx3 (rxs, False)" by auto
                from this[unfolded wf_rx3_def fst_conv snd_conv]
                have wf_rx2: "wf_rx2 (rxs, False)" and "Ball (snd ` set rxs) wf_ts3" using impr by auto 
                with rx_mp[unfolded mp] rx_id 
                have wf_ts: "wf_ts3 ts" by auto
                from this[unfolded wf_ts3_def] have "\<exists> u. u \<in> set ts \<and> is_Var u \<and> find is_Var ts = Some u" 
                  by (induct ts, auto)
                with x have x: "Var x \<in> set ts" by auto
                from t[unfolded rx_id] 
                have t: "t \<in> set ts" "is_Fun t" by auto              
                show ?thesis
                proof (rule pat_instantiate[of n "mp_lr mp" p'', 
                      OF _ disjI2, of "Var x" y t x, folded pat, OF disj, unfolded subst],
                    intro conjI impI refl t)
                  show cvar1: "x \<in> set (the (conflicts (Var x) t))" using t by (cases t, auto simp: conflicts.simps)
                  from x rx_rxs rx_id have xy: "(Var x, Var y) \<in># mp_rx (rxs, b)" unfolding mp_rx_def List.maps_def by auto
                  thus "(Var x, Var y) \<in># mp_lr mp" 
                    unfolding mp_lr_def mp split mp_rx_def by auto
                  from t rx_rxs rx_id have ty: "(t, Var y) \<in># mp_rx (rxs, b)" unfolding mp_rx_def List.maps_def by auto
                  thus "(t, Var y) \<in># mp_lr mp"
                    unfolding mp_lr_def mp split mp_rx_def by auto
                  from rx_rxs rx_id wf_rx2[unfolded wf_rx2_def] have "wf_ts2 ts" by auto
                  from this[unfolded wf_ts2_def wf_ts_no_conflict_alt_def] x t 
                  show cvar2: "conflicts (Var x) t \<noteq> None" by auto
                  from No_ivc[unfolded inf_var_conflict_def] xy ty cvar1 cvar2 show "\<not> inf_sort (snd x)" by blast
                qed
              qed
            qed
          qed
          have tvars: "tvars_pat (\<Union> (pat_list ` set ps)) \<subseteq> {..<n + m} \<times> S"
          proof (safe del: conjI)
            fix yn \<iota>
            assume "(yn,\<iota>) \<in> tvars_pat (\<Union> (pat_list ` set ps))" 
            then obtain pi mp
              where pi: "pi \<in> set ps"
                and mp: "mp \<in> set pi" and y: "(yn,\<iota>) \<in> tvars_match (set mp)"
              unfolding tvars_pat_def pat_list_def by force
            from pi[unfolded ps_def set_map subst_pat_problem_list_def subst_match_problem_list_def, simplified] 
            obtain \<tau> where tau: "\<tau> \<in> set (\<tau>s_list n x)" and pi: "pi = map (map (subst_left \<tau>)) p'l" by auto
            from tau[unfolded \<tau>s_list_def]
            obtain info where infoCl: "info \<in> set (Cl (snd x))" and tau: "\<tau> = \<tau>c n x info" by auto
            from Cl_len[of "snd x"] this(1) have len: "length (snd info) \<le> m" by force
            from mp[unfolded pi set_map] obtain mp' where mp': "mp' \<in> set p'l" and mp: "mp = map (subst_left \<tau>) mp'" by auto
            from y[unfolded mp tvars_match_def image_comp o_def set_map]
            obtain pair where *: "pair \<in> set mp'" "(yn,\<iota>) \<in> vars (fst (subst_left \<tau> pair))" by auto
            obtain s t where pair: "pair = (s,t)" by force
            from *[unfolded pair] have st: "(s,t) \<in> set mp'" and y: "(yn,\<iota>) \<in> vars (s \<cdot> \<tau>)" unfolding subst_left_def by auto
            from y[unfolded vars_term_subst, simplified]
            obtain z where z: "z \<in> vars s" and y: "(yn,\<iota>) \<in> vars (\<tau> z)" by auto
            obtain f ss where info: "info = (f,ss)" by (cases info, auto)
            with len have len: "length ss \<le> m" by auto
            define ts :: "('f,_)term list" where "ts = map Var (zip [n..<n + length ss] ss)" 
            from tau[unfolded \<tau>c_def info split]
            have tau: "\<tau> = subst x (Fun f ts)" unfolding ts_def by auto
            from infoCl[unfolded Cl info]
            have f: "f : ss \<rightarrow> snd x in C" by auto
            from C_sub_S[OF this] have ssS: "set ss \<subseteq> S" by simp
            from ssS
            have "vars (Fun f ts) \<subseteq> {..< n + length ss} \<times> S" unfolding ts_def by (auto simp: set_zip)
            also have "\<dots> \<subseteq> {..< n + m} \<times> S" using len by auto
            finally have subst: "vars (Fun f ts) \<subseteq> {..< n + m} \<times> S" by auto
            show "yn \<in> {..<n + m} \<and> \<iota> \<in> S"
            proof (cases "z = x")
              case True
              with y subst tau show ?thesis by force
            next
              case False
              hence "\<tau> z = Var z" unfolding tau by (auto simp: subst_def)
              with y have "z = (yn,\<iota>)" by auto
              with z have y: "(yn,\<iota>) \<in> vars s" by auto
              with st have "(yn,\<iota>) \<in> tvars_match (set mp')" unfolding tvars_match_def by force
              with mp' have "(yn,\<iota>) \<in> tvars_pat (set ` set p'l)" unfolding tvars_pat_def by auto
              also have "\<dots> = tvars_pat (pat_mset (pat_mset_list p'l))" 
                by (rule arg_cong[of _ _ tvars_pat], auto simp: pat_mset_list_def image_comp)
              also have "\<dots> = tvars_pat (pat_mset (pat_lr p'))" unfolding id[symmetric] by simp
              also have "\<dots> \<subseteq> {..<n} \<times> S" using varsp' .
              finally show ?thesis by auto
            qed
          qed
          {
            fix pp
            assume pp: "pp \<in># mset (map pat_mset_list ps) + P"         
            have "lvar_cond_pp nl'' pp" 
            proof (cases "pp \<in># P")
              case True
              with lvarsAll have "lvar_cond_pp nl pp" by auto
              with lvar_cond_mono[OF nl] show ?thesis unfolding lvar_cond_pp_def by auto
            next
              case False
              then obtain pp' where pp': "pp' \<in> set ps" and pp: "pp = pat_mset_list pp'" 
                using pp by auto
              from pp'[unfolded ps_def] obtain \<tau> where pp': "pp' = subst_pat_problem_list \<tau> p'l" by auto
              have "lvars_pp pp = lvars_pp (pat_lr p')" 
                unfolding pp pp' id
                unfolding lvars_pp_def lvars_mp_def 
                by (force simp: subst_pat_problem_list_def subst_match_problem_list_def subst_left_def pat_mset_list_def)
              thus ?thesis using lvar_p' unfolding lvar_cond_pp_def by auto
            qed
          }
          with tvars step steps res nl show ?thesis by auto
        next
          case None
          hence impr: improved and Nil: "List.maps (\<lambda>(lx, uu). lx) no_ivc = []" unfolding find_var_def Let_def
            by (auto split: option.splits if_splits list.splits)
          from impr False have "ivc = [] \<or> (\<exists> mp \<in> set no_ivc. fst mp \<noteq> [])" by auto
          with Nil have ivc: "ivc = []" unfolding List.maps_def by force
          {
            fix mp
            assume mp_mem: "mp \<in> set no_ivc" 
            from no_ivc_b[OF mp_mem] obtain lx rx where mp: "mp = (lx,rx,False)" by (cases mp, auto)
            from None[unfolded find_var_def] have no_ivc_lx: "List.maps (\<lambda>(lx, uu). lx) no_ivc = []" by (auto split: list.splits)
            from split_list[OF mp_mem] mp no_ivc_lx have lx: "lx = []" by (cases lx, auto simp: List.maps_def)
            with mp have mp: "mp = ([],rx, False)" by auto
            from impr have "improved = True" by simp
            note None = None[unfolded find_var_def no_ivc_lx list.simps this if_True Let_def]
            from None mp_mem
            have "\<forall>a b. ((a, b) \<notin> set (fst (snd mp))) \<or> (\<forall>t\<in>set b. is_Var t)" 
              by (auto simp: find_None_iff List.maps_def)
            from this[unfolded mp] have only_vars: "(x, ts) \<in> set rx \<Longrightarrow> t \<in> set ts \<Longrightarrow> is_Var t" for x ts t by auto
            from wf[unfolded wf_pat_lr_def] mp_mem have "wf_lr3 mp" using sub by auto
            from this[unfolded wf_lr3_def mp split] have "wf_rx3 (rx, False)" by auto
            from this[unfolded wf_rx3_def] have "wf_rx2 (rx, False)" by auto
            from this[unfolded wf_rx2_def snd_conv fst_conv]
            have wf_ts: "Ball (snd ` set rx) wf_ts2" 
              and no_inf: "\<not> inf_var_conflict (mp_mset (mp_rx (rx, False)))" 
              and dist: "distinct (map fst rx)" by auto
            {
              fix x ts t
              assume xts: "(x,ts) \<in> set rx" and t: "t \<in> set ts" 
              from only_vars[OF this] obtain y where ty: "t = Var y" by auto
              from xts wf_ts have "wf_ts2 ts" by auto
              from this[unfolded wf_ts2_def wf_ts_no_conflict_alt_def] t
              have len: "2 \<le> length ts" and dist: "distinct ts"  and no_conf: "\<And> s. s \<in> set ts \<Longrightarrow> conflicts s t \<noteq> None" by auto
              from t len dist obtain s where s_ts: "s \<in> set ts" and "s \<noteq> t" by (cases ts; cases "tl ts"; auto)
              from only_vars[OF xts this(1)] this(2) ty obtain z where s: "s = Var z" and yz: "y \<noteq> z" by (cases s, auto)
              from t have trx: "(t, Var x) \<in># mp_rx (rx, False)" using xts unfolding mp_rx_def List.maps_def by auto
              from s_ts have srx: "(s, Var x) \<in># mp_rx (rx, False)" using xts unfolding mp_rx_def List.maps_def by auto
              have "conflicts s t = (if snd z = snd y then Some [z, y] else None)" unfolding s ty conflicts.simps using yz by auto 
              with no_conf[OF s_ts] have "conflicts s t = Some [z,y]" by (auto split: if_splits)
              with no_inf[unfolded inf_var_conflict_def, simplified, rule_format, OF trx srx] yz
              have "\<not> inf_sort (snd y)" by (cases y, auto)
              with ty have "\<exists> y. t = Var y \<and> \<not> inf_sort (snd y)" by auto
            } note only_fin_sort_vars = this
            with mp dist wf_ts \<open>wf_rx3 (rx, False)\<close> have "\<exists> rx. mp = ([], rx, False) \<and> Ball (snd ` set rx) wf_ts2 \<and> distinct (map fst rx) \<and>
             wf_rx3 (rx, False) \<and>
            (\<forall> x ts t. (x,ts) \<in> set rx \<longrightarrow> t \<in> set ts \<longrightarrow> (\<exists> y. t = Var y \<and> \<not> inf_sort (snd y)))"             
              by blast
          } note no_ivc_probs = this

          have split_p': "pat_lr p' = pat_lr ivc + pat_lr no_ivc" unfolding Notf f
            unfolding pat_lr_def by (induct p', auto)
          hence p'_no_ivc: "pat_lr p' = pat_lr no_ivc" unfolding ivc pat_lr_def by auto

          let ?fvf = "map (map (map_prod id (map the_Var)) \<circ> fst \<circ> snd) no_ivc" 
          let ?pat = "\<lambda> p. pat_mset_list (pat_of_var_form_list p)" 
          note res = res[unfolded None option.simps Let_def]
          from steps p'_no_ivc
          have "(add_mset (pat_mset_list p) P, add_mset (pat_lr no_ivc) P) \<in> \<Rrightarrow>\<^sup>*" by auto
          also have equiv: "pat_lr no_ivc = ?pat ?fvf" 
            unfolding pat_lr_def pat_of_var_form_list_def match_of_var_form_list_def pat_mset_list_def map_map o_def mp_lr_def 
          proof (intro arg_cong[of _ _ mset] map_cong refl)
            fix mp
            assume "mp \<in> set no_ivc" 
            from no_ivc_probs[OF this] obtain rx where mp: "mp = ([], rx, False)" 
              and rx: "\<And> x tx t. (x,tx) \<in> set rx \<Longrightarrow> t \<in> set tx \<Longrightarrow> \<exists> y. t = Var y" by metis
            have triv: "mp_list (mp_lx ([] :: ((nat \<times> 's) \<times> ('f, 'v) Term.term) list)) + M = M" for M by auto
            show "(case mp of (lx, rx) \<Rightarrow> mp_list (mp_lx lx) + mp_rx rx) =
             mp_list
                (concat
            (map (\<lambda>x. case map_prod id (map the_Var) x of (x, xa) \<Rightarrow> map (\<lambda>v. (Var v, Var x)) xa)
              (fst (snd mp))))" 
              unfolding mp split fst_conv snd_conv mp_rx_def List.maps_def triv
              by (rule arg_cong[of _ _ "\<lambda> xs. mset (concat xs)"], intro map_cong refl, insert rx, force)
          qed
          finally have steps': "(add_mset (pat_mset_list p) P, add_mset (?pat ?fvf) P) \<in> \<Rrightarrow>\<^sup>*" .
          have fvf_res: "finite_var_form_pat C (pat_mset (?pat ?fvf))" 
            unfolding finite_var_form_pat_def equiv[symmetric]
          proof
            fix Mp
            assume "Mp \<in> pat_mset (pat_lr no_ivc)" 
            from this[unfolded pat_lr_def]
            obtain mp where mp_mem: "mp \<in> set no_ivc" and Mp: "Mp = mp_mset (mp_lr mp)" by auto
            from no_ivc_probs[OF mp_mem] obtain rx where
              mp: "mp = ([], rx, False)" and
              dist: "distinct (map fst rx)" and 
              wf_ts: "Ball (snd ` set rx) wf_ts2" and
              no_inf: "\<And> x ts t. (x, ts) \<in> set rx \<Longrightarrow> t \<in> set ts \<Longrightarrow> (\<exists>y. t = Var y \<and> \<not> inf_sort (snd y))" by auto
            show "finite_var_form_match C Mp" 
              unfolding finite_var_form_match_def var_form_match_def
            proof (intro conjI allI impI subsetI)
              fix l x
              assume xl: "(Var x, l) \<in> Mp"
              with Mp mp mp_mem sub have "x \<in> tvars_pat (pat_mset (pat_lr p'))"
                apply (auto simp: tvars_pat_def pat_lr_def mp_lr_def mp_rx_def tvars_match_def intro!: bexI[of _ mp])
                by (metis case_prod_conv term.set_intros(3))
              with varsp' have sxS: "snd x \<in> S" by auto
              from xl[unfolded Mp mp split mp_lr_def mp_rx_def List.maps_def]
              obtain ts y where yts: "(y,ts) \<in> set rx" and xts: "Var x \<in> set ts"  and l: "l = Var y" by auto
              from no_inf[OF yts xts] have "\<not> inf_sort (snd x)" by auto
              then show "finite_sort C (snd x)" by (simp add: inf_sort[OF sxS])
              fix z
              assume "(Var z, l) \<in> Mp" 
              from this[unfolded Mp mp split mp_lr_def mp_rx_def List.maps_def] l
              obtain ts' where yts': "(y,ts') \<in> set rx" and zts: "Var z \<in> set ts'"  by auto
              from dist yts yts' have "ts' = ts" by (metis eq_key_imp_eq_value)
              with zts have zts: "Var z \<in> set ts" (is "?z \<in> _") by auto
              from wf_ts yts have "wf_ts2 ts" by auto
              from this[unfolded wf_ts2_def wf_ts_no_conflict_alt_def] xts zts 
              have "conflicts (Var x) ?z \<noteq> None" by blast
              thus "snd x = snd z" unfolding conflicts.simps by (auto split: if_splits)
            next
              fix pair
              assume "pair \<in> Mp" 
              from this[unfolded Mp mp_lr_def mp split]
              have "pair \<in># mp_rx (rx, False)" by auto
              from this[unfolded mp_rx_def List.maps_def]
              obtain x ts t where "(x,ts) \<in> set rx" "t \<in> set ts" and pair: "pair = (t, Var x)" by auto
              with no_inf[OF this(1-2)] 
              show "pair \<in> range (map_prod Var Var)" by auto
            qed
          qed
          show ?thesis using res 
          proof (intro conjI, force, force, intro impI conjI)
            assume "res = Fin_Var_Form fvf" 
            with res have id: "fvf = ?fvf" by simp
            show improved by fact
            show "(add_mset (pat_mset_list p) P, add_mset (?pat fvf) P) \<in> \<Rrightarrow>\<^sup>*" using steps' id by auto
            show "finite_var_form_pat C (pat_list (pat_of_var_form_list fvf))" using fvf_res
              unfolding id pat_mset_list by auto
            show "Ball (set fvf) (distinct \<circ> map fst)" unfolding id using no_ivc_probs by force
            show "Ball (set (concat fvf)) (distinct \<circ> snd)" 
            proof
              fix xvs
              assume "xvs \<in> set (concat fvf)" 
              from this[unfolded id] obtain c where
                c: "c \<in> set no_ivc" and xvs: "xvs \<in> map_prod id (map the_Var) ` set (fst (snd c))" by auto
              from no_ivc_probs[OF c] obtain rx where *: 
                "c = ([], rx, False)" 
                "Ball (snd ` set rx) wf_ts2" 
                "(\<forall>x ts t. (x, ts) \<in> set rx \<longrightarrow> t \<in> set ts \<longrightarrow> (\<exists>y. t = Var y \<and> \<not> inf_sort (snd y)))" by blast
              from xvs[unfolded *(1)]
              have xvs: "xvs \<in> map_prod id (map the_Var) ` set rx" by auto
              then obtain x ts where mem: "(x,ts) \<in> set rx" and xvs: "xvs = (x,map the_Var ts)" by auto
              from *(2) mem have "wf_ts2 ts" by auto 
              hence dist: "distinct ts" unfolding wf_ts2_def by auto
              show "(distinct \<circ> snd) xvs" unfolding xvs o_def snd_conv
                  distinct_map
              proof (rule conjI[OF dist])
                show "inj_on the_Var (set ts)"   
                  by (auto simp: inj_on_def dest!: *(3)[rule_format, OF mem])
              qed
            qed
          qed
        qed
      qed
    qed
  qed
qed

lemma non_uniq_image_diff: "\<not> UNIQ (\<alpha> ` set vs) \<longleftrightarrow> (\<exists> v \<in> set vs. \<exists> w \<in> set vs. \<alpha> v \<noteq> \<alpha> w)"
  by (smt (verit, ccfv_SIG) Uniq_def image_iff)

lemma pat_complete_via_idl_solver:
  assumes impr: "improved"
    and fvf: "finite_var_form_pat C (pat_list pp)"
    and wf: "wf_pat (pat_list pp)"
    and pp: "pp = pat_of_var_form_list fvf" 
    and dist: "Ball (set fvf) (distinct o map fst)" 
    and dist2: "Ball (set (concat fvf)) (distinct o snd)" 
    and cnf: "cnf = map (map snd) fvf"
  shows "pat_complete C (pat_list pp) \<longleftrightarrow> \<not> fidl_solver (bounds_list (cd_sort \<circ> snd) cnf, dist_pairs_list cnf)"
proof-
  let ?S = S
  note vf = finite_var_form_imp_of_var_form_pat[OF fvf]
  have var_conv: "set (concat (concat cnf)) = tvars_pat (pat_list pp)"
    unfolding cnf pp 
    by (force simp: tvars_pat_def pat_list_def tvars_match_def pat_of_var_form_list_def match_of_var_form_list_def)
  from wf[unfolded wf_pat_iff] cd
  have cd_conv: "v \<in> tvars_pat (pat_list pp) \<Longrightarrow> cd_sort (snd v) = card_of_sort C (snd v)"
    for v by auto
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
      unfolding diff_pairs_of_list dist_pairs_list_def List.maps_def set_map image_comp set_concat o_def
      by force
  qed
  also have "\<dots> = fidl_solvable (bounds_list cd cnf, dist_pairs_list cnf)" 
    unfolding fidl_solvable_def split ..
  also have "\<dots> = fidl_solver (bounds_list cd cnf,dist_pairs_list cnf)" 
  proof (rule sym, rule fidl_solver[OF \<open>improved\<close>, unfolded finite_idl_solver_def, rule_format])
    show "fidl_input (bounds_list cd cnf, dist_pairs_list cnf)" unfolding fidl_input_def split
    proof (intro conjI allI impI)
      show "(x, y) \<in> set (concat (dist_pairs_list cnf)) \<Longrightarrow> z \<in> {x, y} \<Longrightarrow> z \<in> fst ` set (bounds_list cd cnf)" for x y z
        unfolding dist_pairs_list_def bounds_list_def List.maps_def  set_concat set_map image_comp o_def
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
      from this[unfolded dist_pairs_list_def cnf List.maps_def, simplified]
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

text \<open>The soundness property of the implementation, proven by induction
  on the relation that was also used to prove termination of @{term "(\<Rrightarrow>)"}.
  Note that we cannot perform induction on @{term "(\<Rrightarrow>)"} here, since applying
  a decision procedure for finite-var-form problems does not correspond to 
  a @{term "(\<Rrightarrow>)"}-step.\<close>
lemma pats_impl: assumes "\<forall>p \<in> set ps. tvars_pat (pat_list p) \<subseteq> {..<n} \<times> S" 
  and "Ball (set ps) (\<lambda> pp. lvar_cond_pp nl (pat_mset_list pp))" 
  and "\<forall>pp \<in> pat_list ` set ps. wf_pat pp"
  shows "Pats_impl n nl ps = pats_complete C (pat_list ` set ps)" 
proof (insert assms, induct ps arbitrary: n nl rule: wf_induct[OF wf_inv_image[OF wf_trancl[OF wf_rel_pats]], of pats_mset_list])
  case (1 ps n nl)
  note IH = mp[OF spec[OF mp[OF spec[OF mp[OF spec[OF 1(1)]]]]]]
  note wf = 1(4)
  show ?case 
  proof (cases ps)
    case Nil
    show ?thesis unfolding pats_impl.simps[of _ _ _ n nl ps] unfolding Nil by auto
  next
    case (Cons p ps1)
    hence id: "pats_mset_list ps = add_mset (pat_mset_list p) (pats_mset_list ps1)" by auto
    note res = pats_impl.simps[of _ _ _ n nl ps, unfolded Cons list.simps, folded Cons]
    from 1(2)[rule_format, of p] Cons have "tvars_pat (pat_list p) \<subseteq> {..<n} \<times> S" by auto
    note pat_impl = pat_impl[OF refl this]
    from 1(3) have "\<forall>pp \<in># add_mset (pat_mset_list p) (pats_mset_list ps1). lvar_cond_pp nl pp" 
      unfolding Cons by auto
    note pat_impl = pat_impl[OF this, folded id]
    let ?step = "(\<Rrightarrow>) :: (('f,'v,'s)pats_problem_mset \<times> ('f,'v,'s)pats_problem_mset)set" 
    { 
      from rel_P_trans have single: "?step \<subseteq> (\<prec>mul)^-1"  
        unfolding P_step_def by auto
      have "(s,t) \<in> ?step^+ \<Longrightarrow> (t,s) \<in> (\<prec>mul)^+" "(s,t) \<in> ?step^* \<Longrightarrow> (t,s) \<in> (\<prec>mul)^*" for s t 
        using trancl_mono[OF _ single]
         apply (metis converse_iff trancl_converse) 
        using rtrancl_converse rtrancl_mono[OF single] 
        by auto
    } note steps_to_rel = this
    from wf have "wf_pats (pat_list ` set ps)" unfolding wf_pats_def by auto
    note steps_to_equiv = P_steps_pcorrect[OF this[folded pats_mset_list]]
    show ?thesis
    proof (cases "Pat_impl n nl p")
      case Incomplete
      with res have res: "Pats_impl n nl ps = False" by auto
      from pat_impl(1)[OF Incomplete]  
      obtain p' where steps: "(pats_mset_list ps, add_mset p' (pats_mset_list ps1)) \<in> \<Rrightarrow>\<^sup>*" and fail: "pat_fail p'" 
        by auto
      show ?thesis
      proof (cases "add_mset p' (pats_mset_list ps1) = bottom_mset")
        case True
        with res P_steps_pcorrect[OF _ steps, unfolded pats_mset_list] wf 
        show ?thesis by (auto simp: wf_pats_def)
      next
        case False
        from P_failure[OF fail False] 
        have "(add_mset p' (pats_mset_list ps1), bottom_mset) \<in> \<Rrightarrow>" unfolding P_step_def by auto
        with steps have "(pats_mset_list ps, bottom_mset) \<in> \<Rrightarrow>\<^sup>*" by auto
        from steps_to_equiv[OF this] res show ?thesis unfolding pats_mset_list by simp
      qed
    next
      case (New_Problems triple)
      then obtain n2 nl2 ps2 where Some: "Pat_impl n nl p = New_Problems (n2,nl2,ps2)" by (cases triple) auto
      with res have res: "Pats_impl n nl ps = Pats_impl n2 nl2 (ps2 @ ps1)" by auto
      from pat_impl(2)[OF Some]
      have steps: "(pats_mset_list ps, mset (map pat_mset_list (ps2 @ ps1))) \<in> \<Rrightarrow>\<^sup>+" 
          and vars: "tvars_pat (\<Union> (pat_list ` set ps2)) \<subseteq> {..<n2} \<times> S"
          and lvars: "(\<forall>pp\<in>#mset (map pat_mset_list ps2) + pats_mset_list ps1. lvar_cond_pp nl2 pp)" 
          and n2: "n \<le> n2" by auto        
      from steps_to_rel(1)[OF steps] have rel: "(ps2 @ ps1, ps) \<in> inv_image (\<prec>mul\<^sup>+) pats_mset_list" 
        by auto
      have vars: "\<forall>p\<in>set (ps2 @ ps1). tvars_pat (pat_list p) \<subseteq> {..<n2} \<times> S"
      proof
        fix p
        assume "p \<in> set (ps2 @ ps1)" 
        hence "p \<in> set ps2 \<or> p \<in> set ps1" by auto
        thus "tvars_pat (pat_list p) \<subseteq> {..<n2} \<times> S" 
        proof
          assume "p \<in> set ps2" 
          hence "tvars_pat (pat_list p) \<subseteq> tvars_pat (\<Union> (pat_list ` set ps2))" 
            unfolding tvars_pat_def by auto
          with vars show ?thesis by auto
        next
          assume "p \<in> set ps1" 
          hence "p \<in> set ps" unfolding Cons by auto
          from 1(2)[rule_format, OF this] n2 show ?thesis by auto
        qed
      qed
      have lvars: "\<forall>pp\<in>set (ps2 @ ps1). lvar_cond_pp nl2 (pat_mset_list pp)" 
        using lvars unfolding lvar_cond_pp_def by auto
      note steps_equiv = steps_to_equiv[OF trancl_into_rtrancl[OF steps]]
      from steps_equiv have "wf_pats (pats_mset (mset (map pat_mset_list (ps2 @ ps1))))" by auto
      hence wf2: "Ball (pat_list ` set (ps2 @ ps1)) wf_pat" unfolding wf_pats_def pats_mset_list[symmetric]
        by auto
      have "Pats_impl n nl ps = Pats_impl n2 nl2 (ps2 @ ps1)" unfolding res by simp
      also have "\<dots> = pats_complete C (pat_list ` set (ps2 @ ps1))"
        using mp[OF IH[OF rel vars lvars] wf2] .
      also have "\<dots> = pats_complete C (pat_list ` set ps)" using steps_equiv 
        unfolding pats_mset_list[symmetric] by auto
      finally show ?thesis .
    next
      case FVF: (Fin_Var_Form fvf)
      let ?pat = "\<lambda> p. pat_mset_list (pat_of_var_form_list p)" 
      let ?pat' = "\<lambda> p. pat_list (pat_of_var_form_list p)" 
      from pat_impl(3)[OF FVF] 
      have steps: "(pats_mset_list ps, add_mset (?pat fvf) (pats_mset_list ps1)) \<in> \<Rrightarrow>\<^sup>*" 
        and ifvf: improved "finite_var_form_pat C (?pat' fvf)" 
        and dist: "Ball (set fvf) (distinct \<circ> map fst)" 
        and dist2: "Ball (set (concat fvf)) (distinct \<circ> snd)" by auto
      have "wf_pats (pats_mset (pats_mset_list ps))" 
        using wf unfolding wf_pats_def pats_mset_list .
      from P_steps_pcorrect[OF this steps]
      have wf': "wf_pats (pats_mset (add_mset (?pat fvf) (pats_mset_list ps1)))"
        and red: "pats_complete C (pats_mset (pats_mset_list ps)) =
        pats_complete C (pats_mset (add_mset (?pat fvf) (pats_mset_list ps1)))"
        and "wf_pat (pat_mset (?pat fvf))" unfolding wf_pats_def by auto
      from this(3)[unfolded pat_mset_list]
      have wf_fvf: "wf_pat (pat_list (pat_of_var_form_list fvf))" .
      have "(pats_mset_list ps1, add_mset (?pat fvf) (pats_mset_list ps1)) \<in> \<prec>mul" 
        unfolding rel_pats_def by (simp add: subset_implies_mult)
      with steps_to_rel(2)[OF steps]
      have "(pats_mset_list ps1, pats_mset_list ps) \<in> \<prec>mul\<^sup>+" by auto
      hence "(ps1, ps) \<in> inv_image (\<prec>mul\<^sup>+) pats_mset_list" by auto
      note IH = IH[OF this]
      from 1(2) Cons have "\<forall>p\<in>set ps1. tvars_pat (pat_list p) \<subseteq> {..<n} \<times> S" by auto
      note IH = IH[OF this]
      from 1(3) Cons have "\<forall>pp\<in>set ps1. lvar_cond_pp nl (pat_mset_list pp)" by auto
      note IH = IH[OF this]
      with 1(4) Cons have IH: "Pats_impl n nl ps1 = pats_complete C (pat_list ` set ps1)" by auto
      note via_idl = pat_complete_via_idl_solver[OF ifvf wf_fvf refl dist dist2 refl] 
      let ?cnf = "(map (map snd) fvf)" 
      from FVF res have "Pats_impl n nl ps =
        (\<not> fidl_solver (bounds_list (cd_sort \<circ> snd) ?cnf, dist_pairs_list ?cnf) \<and> Pats_impl n nl ps1)" 
        by (auto simp: Let_def)
      also have "\<dots> = (pat_complete C (pat_list (pat_of_var_form_list fvf)) \<and> pats_complete C (pat_list ` set ps1))" 
        unfolding via_idl IH by simp
      also have "\<dots> = pats_complete C (pats_mset (pats_mset_list ps))" 
        unfolding steps_to_equiv[OF steps, THEN conjunct2]
        by (smt (z3) add_mset_commute comp_def image_iff insert_noteq_member mset_add pat_mset_list
            pats_mset_list union_single_eq_member)
      also have "\<dots> = pats_complete C (pat_list ` set ps)" 
        unfolding pats_mset_list ..
      finally show ?thesis .
    qed
  qed
qed


text \<open>Consequence: partial correctness of the list-based implementation on well-formed inputs\<close>

corollary pat_complete_impl: 
  assumes wf: "snd ` \<Union> (vars ` fst ` set (concat (concat P))) \<subseteq> S" 
  shows "Pat_complete_impl (P :: ('f,'v,'s)pats_problem_list) \<longleftrightarrow> pats_complete C (pat_list ` set P)" 
proof - 
  have wf: "Ball (pat_list ` set P) wf_pat" 
    unfolding pat_list_def wf_pat_def wf_match_def tvars_match_def using wf[unfolded set_concat image_comp] by force
  let ?l = "(List.maps (map fst o vars_term_list o fst) (concat (concat P)))" 
  define n where "n = Suc (max_list ?l)" 
  have n: "\<forall>p\<in>set P. tvars_pat (pat_list p) \<subseteq> {..<n} \<times> S" 
  proof (safe)
    fix p x \<iota>
    assume p: "p \<in> set P" and xp: "(x,\<iota>) \<in> tvars_pat (pat_list p)" 
    hence "x \<in> set ?l" unfolding List.maps_def tvars_pat_def tvars_match_def pat_list_def 
      by force
    from max_list[OF this] have "x < n" unfolding n_def by auto
    thus "x < n" by auto
    from xp p wf
    show "\<iota> \<in> S" by (auto simp: wf_pat_iff)
  qed  
  show ?thesis
  proof (cases improved)
    case False
    have 0: "\<forall>p\<in>set P. lvar_cond_pp 0 (pat_mset_list p)" 
      unfolding lvar_cond_pp_def lvar_cond_def allowed_vars_def using False by auto
    have "Pat_complete_impl P = Pats_impl n 0 P" 
      unfolding pat_complete_impl_def n_def Let_def using False by auto
    from pats_impl[OF n 0 wf, folded this]
    show ?thesis .
  next
    case True
    let ?r_mp = "map (apsnd (map_vars renVar))" 
    let ?r = "map ?r_mp" 
    let ?Q = "map ?r P" 
    have "Pat_complete_impl P = Pats_impl n 0 ?Q" 
      unfolding pat_complete_impl_def n_def Let_def using True by auto
    also have "\<dots> = pats_complete C (pat_list ` set ?Q)" 
    proof (rule pats_impl)
      show "\<forall> p \<in> set ?Q. tvars_pat (pat_list p) \<subseteq> {..<n} \<times> S" 
      proof
        fix rp 
        assume "rp \<in> set ?Q" 
        then obtain p where p: "p \<in> set P" and rp: "rp = ?r p" by auto
        have id: "tvars_pat (pat_list rp) = tvars_pat (pat_list p)" 
          unfolding pat_list_def rp tvars_pat_def tvars_match_def by force
        with n p show "tvars_pat (pat_list rp) \<subseteq> {..<n} \<times> S" by auto
      qed
      show "Ball (pat_list ` set ?Q) wf_pat" 
      proof -
        {
          fix rp
          assume rp: "rp \<in> set ?Q" 
          then obtain p where "p \<in> set P" and rp: "rp = ?r p" by auto
          from this(1) wf have "wf_pat (pat_list p)" by auto
          hence "wf_pat (pat_list rp)" unfolding wf_pat_def wf_match_def
            unfolding pat_list_def rp tvars_match_def by force
        }
        thus ?thesis by blast
      qed
      show "\<forall> p \<in> set ?Q.  lvar_cond_pp 0 (pat_mset_list p)" 
      proof
        fix rp
        assume "rp \<in> set ?Q" 
        then obtain p where rp: "rp = ?r p" by auto
        show "lvar_cond_pp 0 (pat_mset_list rp)" 
          unfolding lvar_cond_pp_def lvar_cond_def
        proof
          fix x
          assume "x \<in> lvars_pp (pat_mset_list rp)" 
          from this[unfolded lvars_pp_def lvars_mp_def pat_mset_list_def rp]
          obtain t :: "('f, 'v) term" where "x \<in> vars (map_vars renVar t)" by auto
          hence "x \<in> range renVar" by (induct t, auto)
          thus "x \<in> allowed_vars 0" unfolding allowed_vars_def by auto
        qed
      qed
    qed
    also have "\<dots> = pats_complete C (pat_list ` set P)" 
      unfolding set_map image_comp 
      unfolding Ball_image_comp o_def
    proof (intro ball_cong[OF refl])
      fix p
      assume p: "p \<in> set P" 
      have id: "pat_list (map (map (apsnd (map_vars renVar))) p) = (\<lambda> mp. apsnd (map_vars renVar) ` mp) ` pat_list p" 
        unfolding pat_list_def set_map image_comp o_def ..
      note bex = bex_simps(7) (* (\<exists>x\<in> f ` A. P x) = (\<exists>x\<in> A. P (f x)) *)
      from wf p
      have wfp: "wf_pat (pat_list p)"
        by (fastforce simp: subset_iff wf_pat_def wf_match_def tvars_match_def)
      from wf p
      have wf2: "wf_pat (pat_list (?r p))"
        by (fastforce simp: id subset_iff wf_pat_def wf_match_def tvars_match_def)
      show "pat_complete C (pat_list (?r p)) = pat_complete C (pat_list p)" 
        apply (unfold wf_pat_complete_iff[OF wfp] wf_pat_complete_iff[OF wf2])
        apply (unfold id bex)
      proof (rule all_cong, rule bex_cong[OF refl])
        fix \<sigma> mp
        have id: "map_vars renVar = (\<lambda> t. t \<cdot> (Var o renVar))" using map_vars_term_eq[of renVar] by auto
        show "match_complete_wrt \<sigma> (apsnd (map_vars renVar) ` mp) = match_complete_wrt \<sigma> mp" (is "?m1 = ?m2")
        proof
          assume ?m1
          from this[unfolded match_complete_wrt_def] obtain \<mu>
            where match: "\<And> t l.  (t, l) \<in> mp \<Longrightarrow> t \<cdot> \<sigma> = map_vars renVar l \<cdot> \<mu>" by force
          show ?m2 unfolding match_complete_wrt_def
            by (intro exI[of _ "(Var o renVar) \<circ>\<^sub>s \<mu>"], insert match[unfolded id], auto)
        next
          assume ?m2
          from this[unfolded match_complete_wrt_def] obtain \<mu>
            where match: "\<And> t l.  (t, l) \<in> mp \<Longrightarrow> t \<cdot> \<sigma> = l \<cdot> \<mu>" by force
          {
            fix t
            have "t \<cdot> (Var \<circ> renVar) \<cdot> (Var \<circ> the_inv renVar) \<cdot> \<mu> = t \<cdot> \<mu>" 
              unfolding subst_subst 
            proof (intro term_subst_eq)
              fix x
              from renaming_ass[rule_format, OF \<open>improved\<close>, unfolded renaming_funs_def]
              have inj: "inj renVar" by auto
              from the_inv_f_f[OF this]
              show "((Var \<circ> renVar) \<circ>\<^sub>s (Var \<circ> the_inv renVar) \<circ>\<^sub>s \<mu>) x = \<mu> x"                 
                by (simp add: o_def subst_compose_def)
            qed
          }
          thus ?m1 unfolding match_complete_wrt_def
            by (intro exI[of _ "(Var o the_inv renVar) \<circ>\<^sub>s \<mu>"], insert match, auto simp: id)
        qed
      qed
    qed
    finally show ?thesis .
  qed
qed
end
end

subsection \<open>Getting the result outside the locale with assumptions\<close>

text \<open>We next lift the results for the list-based implementation out of the locale.
  Here, we use the existing algorithms to decide non-empty sorts @{const decide_nonempty_sorts} 
  and to compute the infinite sorts @{const compute_inf_sorts}.\<close>
lemma hastype_in_map_of: "distinct (map fst l) \<Longrightarrow> x : \<sigma> in map_of l \<longleftrightarrow> (x,\<sigma>) \<in> set l"
  by (auto simp: hastype_def)

lemma fun_hastype_in_map_of: "distinct (map fst l) \<Longrightarrow>
  x : \<sigma>s \<rightarrow> \<tau> in map_of l \<longleftrightarrow> ((x,\<sigma>s),\<tau>) \<in> set l"
  by (auto simp: fun_hastype_def)

definition constr_list where "constr_list Cs s = map fst (filter ((=) s o snd) Cs)"

text \<open>extract all sorts from a ssignature (input and target sorts)\<close>
definition sorts_of_ssig_list :: "(('f \<times> 's list) \<times> 's)list \<Rightarrow> 's list" where
  "sorts_of_ssig_list Cs = remdups (List.maps (\<lambda> ((f,ss),s). s # ss) Cs)" 

lemma sorts_of_ssig_list:
  assumes "((f,\<sigma>s),\<tau>) \<in> set Cs"
  shows "set \<sigma>s \<subseteq> set (sorts_of_ssig_list Cs)" "\<tau> \<in> set (sorts_of_ssig_list Cs)"
  using assms
  by (auto simp: sorts_of_ssig_list_def List.maps_def)

definition max_arity_list where
  "max_arity_list Cs = max_list (map (length o snd o fst) Cs)"

lemma max_arity_list:
  "((f,\<sigma>s),\<tau>) \<in> set Cs \<Longrightarrow> length \<sigma>s \<le> max_arity_list Cs"
  by (force simp: max_arity_list_def o_def intro! :max_list)

locale pattern_completeness_list =
  fixes Cs
  assumes dist: "distinct (map fst Cs)" 
  and inhabited: "decide_nonempty_sorts (sorts_of_ssig_list Cs) Cs = None"
begin

lemma nonempty_sort: "\<And> \<sigma>. \<sigma> \<in> set (sorts_of_ssig_list Cs) \<Longrightarrow> \<not> empty_sort (map_of Cs) \<sigma>"
  using decide_nonempty_sorts(1)[OF dist inhabited]
  by (auto elim: not_empty_sortE)

lemma compute_inf_sorts: "\<sigma> \<in> compute_inf_sorts Cs \<longleftrightarrow> \<not> finite_sort (map_of Cs) \<sigma>"
    apply (subst compute_inf_sorts(2)[OF _ dist])
    using nonempty_sort
    by (auto intro!:nonempty_sort simp: fun_hastype_in_map_of[OF dist] dest!: sorts_of_ssig_list(1))

lemma compute_card_sorts: "snd (compute_inf_card_sorts Cs) = card_of_sort (map_of Cs)"
  apply (rule compute_inf_card_sorts(2)[OF refl _ dist surjective_pairing])
  by (auto intro!: nonempty_sort simp: fun_hastype_in_map_of[OF dist] dest!: sorts_of_ssig_list(1))

sublocale pattern_completeness_context_with_assms
  improved "set (sorts_of_ssig_list Cs)" "map_of Cs" "max_arity_list Cs" "constr_list Cs"
  "\<lambda> s. s \<in> compute_inf_sorts Cs"
  "snd (compute_inf_card_sorts Cs)"
  for improved
proof
  {
    fix f ss s
    assume "f : ss \<rightarrow> s in map_of Cs"
    hence "((f,ss),s) \<in> set Cs" by (auto dest!: fun_hastypeD map_of_SomeD)
    from sorts_of_ssig_list[OF this] max_arity_list[OF this]
    show "insert s (set ss) \<subseteq> set (sorts_of_ssig_list Cs)" "length ss \<le> max_arity_list Cs"
      by auto
  }
  show "finite (dom (map_of Cs))" by (auto simp: finite_dom_map_of)
  show "set (constr_list Cs s) = {(f,ss). f : ss \<rightarrow> s in map_of Cs}" for s
    unfolding constr_list_def set_map o_def using dist
    by (force simp: fun_hastype_def)
  {
    fix f ss s
    assume "(f,ss) \<in> set (constr_list Cs s)" 
    hence "((f,ss),s) \<in> set Cs" unfolding constr_list_def by auto
    from max_arity_list[OF this] have "length ss \<le> max_arity_list Cs" by auto
  }
  then show m: "\<forall>a\<in>length ` snd ` set (constr_list Cs s). a \<le> max_arity_list Cs" for s by auto
qed (auto simp: compute_inf_sorts nonempty_sort compute_card_sorts)

thm pat_complete_impl
thm pat_complete_lin_impl

end


text \<open>Next we are also leaving the locale that fixed the common parameters,
  and chooses suitable values.\<close> 

text \<open>Finally: a pattern completeness decision procedure for arbitrary inputs,
  assuming sensible inputs;
  this is the old decision procedure\<close>

context 
  fixes m :: nat \<comment> \<open>upper bound on arities of constructors\<close>
    and Cl :: "'s \<Rightarrow> ('f \<times> 's list)list" \<comment> \<open>a function to compute all constructors of given sort as list\<close> 
    and Is :: "'s \<Rightarrow> bool" \<comment> \<open>a function to indicate whether a sort is infinite\<close>
    and Cd :: "'s \<Rightarrow> nat" \<comment> \<open>a function to compute finite cardinality of sort\<close>
begin

definition "pat_complete_impl_old = pattern_completeness_context.pat_complete_impl m Cl Is Cd False undefined undefined undefined undefined"
definition "pats_impl_old = pattern_completeness_context.pats_impl m Cl Is Cd False undefined undefined undefined" 
definition "pat_impl_old = pattern_completeness_context.pat_impl m Cl Is False undefined undefined" 
definition "pat_inner_impl_old = pattern_completeness_context.pat_inner_impl Is False undefined"  
definition "match_decomp'_impl_old = pattern_completeness_context.match_decomp'_impl Is False undefined" 

definition find_var_old :: "('f,'v,'s)match_problem_lr list \<Rightarrow> _" where 
  "find_var_old p = (case List.maps (\<lambda> (lx,_). lx) p of
      (x,t) # _ \<Rightarrow> x
    | [] \<Rightarrow> (let (_,rx,b) = hd p
         in case hd rx of (x, s # t # _) \<Rightarrow> hd (the (conflicts s t))))" 

lemma find_var_old: "find_var False p = Some (find_var_old p)" 
  unfolding find_var_old_def find_var_def if_False by (auto split: list.splits)

lemmas pat_complete_impl_old_code[code] = pattern_completeness_context.pat_complete_impl_def[of m Cl Is Cd False undefined undefined undefined undefined,
    folded pat_complete_impl_old_def pats_impl_old_def,
    unfolded if_False Let_def]

private lemma triv_ident: "False \<and> x \<longleftrightarrow> False" "True \<and> x \<longleftrightarrow> x" by auto

lemmas pat_impl_old_code[code] = pattern_completeness_context.pat_impl_def[of m Cl Is False undefined undefined, 
    folded pat_impl_old_def pat_inner_impl_old_def,
    unfolded find_var_old option.simps triv_ident if_False] 

lemma pats_impl_old_code[code]: 
  "pats_impl_old n nl ps =
    (case ps of [] \<Rightarrow> True
     | p # ps1 \<Rightarrow>
         (case pat_impl_old n nl p of Incomplete \<Rightarrow> False
         | New_Problems (n', nl', ps2) \<Rightarrow> pats_impl_old n' nl' (ps2 @ ps1)))" 
  unfolding pats_impl_old_def pattern_completeness_context.pats_impl.simps[of _ _ _ _ _ _ _ _ _ _ ps]
  unfolding pat_impl_old_def[symmetric]
  unfolding pat_impl_old_code
  by (auto split: list.splits option.splits)

lemmas match_decomp'_impl_old_code[code] =
  pattern_completeness_context.match_decomp'_impl_def[of Is False undefined, folded match_decomp'_impl_old_def,
  unfolded pattern_completeness_context.apply_decompose'_def triv_ident if_False]
 

lemmas pat_inner_impl_old_code[code] =
  pattern_completeness_context.pat_inner_impl.simps[of Is False undefined, folded pat_inner_impl_old_def match_decomp'_impl_old_def]

context
  fixes 
        C :: "('f \<times> 's list) \<Rightarrow> 's option" 
    and rn :: "nat \<Rightarrow> 'v"
    and rv :: "'v \<Rightarrow> 'v"
    and fidl_solver :: "((nat\<times>'s) \<times> int)list \<times> ((nat\<times>'s) \<times> (nat\<times>'s))list list \<Rightarrow> bool" 
begin
definition "pat_complete_impl_new = pattern_completeness_context.pat_complete_impl m Cl Is Cd True C rn rv fidl_solver"
definition "pats_impl_new = pattern_completeness_context.pats_impl m Cl Is Cd True C rn fidl_solver "
definition "pat_impl_new = pattern_completeness_context.pat_impl m Cl Is True C rn" 
definition "pat_inner_impl_new = pattern_completeness_context.pat_inner_impl Is True rn"  
definition "match_decomp'_impl_new = pattern_completeness_context.match_decomp'_impl Is True rn"
definition "find_var_new = find_var True"

lemmas pat_complete_impl_new_code[code] = pattern_completeness_context.pat_complete_impl_def[of m Cl Is Cd True C rn rv fidl_solver,
    folded pat_complete_impl_new_def pats_impl_new_def,
    unfolded if_True Let_def]

lemmas pat_impl_new_code[code] = pattern_completeness_context.pat_impl_def[of m Cl Is True C rn, 
    folded pat_impl_new_def pat_inner_impl_new_def find_var_new_def,
    unfolded triv_ident]

lemmas pats_impl_new_code[code] = pattern_completeness_context.pats_impl.simps[of m Cl Is Cd True C rn fidl_solver,
    folded pats_impl_new_def pat_impl_new_def]

lemmas match_decomp'_impl_new_code[code] =
  pattern_completeness_context.match_decomp'_impl_def[of Is True rn, 
    folded match_decomp'_impl_new_def,
  unfolded pattern_completeness_context.apply_decompose'_def triv_ident]
 
lemmas pat_inner_impl_new_code[code] =
  pattern_completeness_context.pat_inner_impl.simps[of Is True rn, 
    folded pat_inner_impl_new_def match_decomp'_impl_new_def]

lemmas find_var_new_code[code] = 
  find_var_def[of True, 
    folded find_var_new_def,
    unfolded if_True]

end
end

definition decide_pat_complete :: "(('f \<times> 's list) \<times> 's)list \<Rightarrow> ('f,'v,'s)pats_problem_list \<Rightarrow> bool" where
  "decide_pat_complete Cs P = (let 
      m = max_arity_list Cs;
      Cl = constr_list Cs; 
      (IS,CD) = compute_inf_card_sorts Cs
     in pat_complete_impl_old m Cl (\<lambda> s. s \<in> IS) CD) P" 

definition decide_pat_complete_lin :: "(('f \<times> 's list) \<times> 's)list \<Rightarrow> ('f,'v,'s)pats_problem_list \<Rightarrow> bool" where
  "decide_pat_complete_lin Cs P = (let 
      m = max_arity_list Cs;
      Cl = constr_list Cs
     in pattern_completeness_context.pat_complete_lin_impl m Cl P)" 

(* the decision procedure of the FSCD paper, but 
   implementing the linear rules *)
theorem decide_pat_complete_lin:
  assumes dist: "distinct (map fst Cs)" 
    and non_empty_sorts: "decide_nonempty_sorts (sorts_of_ssig_list Cs) Cs = None" 
    and P: "snd ` \<Union> (vars ` fst ` set (concat (concat P))) \<subseteq> set (sorts_of_ssig_list Cs)"
    and left_linear: "Ball (set P) ll_pp" 
  shows "decide_pat_complete_lin Cs P = pats_complete (map_of Cs) (pat_list ` set P)"
proof-
  interpret pattern_completeness_list Cs
    apply unfold_locales
    using dist non_empty_sorts.
  show ?thesis
    unfolding decide_pat_complete_lin_def Let_def
    by (rule pat_complete_lin_impl[OF P left_linear])
qed

(* the decision procedure of FSCD paper *)
theorem decide_pat_complete:
  assumes dist: "distinct (map fst Cs)" 
    and non_empty_sorts: "decide_nonempty_sorts (sorts_of_ssig_list Cs) Cs = None" 
    and P: "snd ` \<Union> (vars ` fst ` set (concat (concat P))) \<subseteq> set (sorts_of_ssig_list Cs)"
  shows "decide_pat_complete Cs P = pats_complete (map_of Cs) (pat_list ` set P)"
proof-
  interpret pattern_completeness_list Cs
    apply unfold_locales
    using dist non_empty_sorts.
  show ?thesis
    unfolding decide_pat_complete_def Let_def pat_complete_impl_old_def
    apply (unfold case_prod_beta)
    apply (rule pat_complete_impl[OF _ _ _ P]) by auto
qed

(* the improved decision procedure for pattern completeness that 
   stops at finite-variable forms, and then 
   encodes these problems into finite integer difference logic and calls 
   an fidl-solver *)
definition decide_pat_complete_fidl :: "_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> (('f \<times> 's list) \<times> 's)list \<Rightarrow> ('f,'v,'s)pats_problem_list \<Rightarrow> bool" where
  "decide_pat_complete_fidl rn rv idl Cs P = (let 
      m = max_arity_list Cs;
      Cl = constr_list Cs; 
      Cm = Mapping.of_alist Cs;
      (IS,CD) = compute_inf_card_sorts Cs
     in pat_complete_impl_new m Cl (\<lambda> s. s \<in> IS) CD (Mapping.lookup Cm))  rn rv idl P" 

definition "fvf_pp_list pp =
  [[y. (t', Var y) \<leftarrow> pp, t' = t]. t \<leftarrow> remdups (map fst pp)]"


theorem decide_pat_complete_fidl:
  assumes dist: "distinct (map fst Cs)" 
    and non_empty_sorts: "decide_nonempty_sorts (sorts_of_ssig_list Cs) Cs = None" 
    and P: "snd ` \<Union> (vars ` fst ` set (concat (concat P))) \<subseteq> set (sorts_of_ssig_list Cs)"
    and ren: "renaming_funs rn rv" 
    and fidl_solver: "finite_idl_solver fidl_solver"
  shows "decide_pat_complete_fidl rn rv fidl_solver Cs P \<longleftrightarrow> pats_complete (map_of Cs) (pat_list ` set P)"
    (is "?l \<longleftrightarrow> ?r")
proof -
  interpret pattern_completeness_list Cs
    apply unfold_locales
    using dist non_empty_sorts.
  have nemp:
    "\<forall> f \<tau>s \<tau> \<tau>'. f : \<tau>s \<rightarrow> \<tau> in map_of Cs \<longrightarrow> \<tau>' \<in> set \<tau>s \<longrightarrow> \<not> empty_sort (map_of Cs) \<tau>'"
    using C_sub_S by (auto intro!: nonempty_sort)
  obtain inf cd where "compute_inf_card_sorts Cs = (inf,cd)" by force
  with compute_inf_card_sorts(2,3)[OF refl nemp dist this]
  have cics: "compute_inf_card_sorts Cs = (compute_inf_sorts Cs,card_of_sort (map_of Cs))"
    by auto
  have Cm: "Mapping.lookup (Mapping.of_alist Cs) = map_of Cs" using dist
    using lookup_of_alist by fastforce
  show ?thesis
    apply (unfold decide_pat_complete_fidl_def Let_def case_prod_beta)
    unfolding pat_complete_impl_new_def
    using pat_complete_impl[OF Cm ren fidl_solver P]
    by auto
qed

export_code decide_pat_complete_lin checking 
export_code decide_pat_complete checking 
export_code decide_pat_complete_fidl checking 

end