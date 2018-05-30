(*
    Authors:    René Thiemann
    License:    BSD
*)
subsubsection \<open>Implementation via Arrays\<close>

theory LLL_Mu_Integer_Impl
  imports LLL
   List_Representation
   LLL_Integer_Equations
   Gram_Schmidt_Int
begin

hide_fact (open) Word.inc_i

type_synonym LLL_dmu_d_state = "int vec list_repr \<times> int iarray iarray \<times> int iarray"

fun fi_state :: "LLL_dmu_d_state \<Rightarrow> int vec" where
  "fi_state (f,mu,d) = get_nth_i f" 

fun fim1_state :: "LLL_dmu_d_state \<Rightarrow> int vec" where
  "fim1_state (f,mu,d) = get_nth_im1 f" 

fun d_state :: "LLL_dmu_d_state \<Rightarrow> nat \<Rightarrow> int" where
  "d_state (f,mu,d) i = d !! i" 

fun fs_state :: "LLL_dmu_d_state \<Rightarrow> int vec list" where
  "fs_state (f,mu,d) = of_list_repr f" 

fun upd_fi_mu_state :: "LLL_dmu_d_state \<Rightarrow> nat \<Rightarrow> int vec \<Rightarrow> int iarray \<Rightarrow> LLL_dmu_d_state" where
  "upd_fi_mu_state (f,mu,d) i fi mu_i = (update_i f fi, iarray_update mu i mu_i,d)" 

fun small_fs_state :: "LLL_dmu_d_state \<Rightarrow> int vec list" where
  "small_fs_state (f,_) = fst f" 

fun dmu_ij_state :: "LLL_dmu_d_state \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int" where
  "dmu_ij_state (f,mu,_) i j = mu !! i !! j" 

fun inc_state :: "LLL_dmu_d_state \<Rightarrow> LLL_dmu_d_state" where
  "inc_state (f,mu,d) = (inc_i f, mu, d)" 

fun basis_reduction_add_rows_loop where
  "basis_reduction_add_rows_loop n state i j [] = state" 
| "basis_reduction_add_rows_loop n state i sj (fj # fjs) = (
     let fi = fi_state state;
         dsj = d_state state sj;
         j = sj - 1;
         c = floor_ceil_num_denom (dmu_ij_state state i j) dsj;
         state' = (if c = 0 then state else upd_fi_mu_state state i (vec n (\<lambda> i. fi $ i - c * fj $ i)) 
             (IArray.of_fun (\<lambda> jj. let mu = dmu_ij_state state i jj in 
                  if jj < j then mu - c * dmu_ij_state state j jj else 
                  if jj = j then mu - dsj * c else mu) i))
      in basis_reduction_add_rows_loop n state' i j fjs)"

text \<open>More efficient code which breaks abstraction of state.\<close>
 
lemma basis_reduction_add_rows_loop_code: 
  "basis_reduction_add_rows_loop n state i sj (fj # fjs) = (
     case state of ((f1,f2),mus,ds) \<Rightarrow> 
     let fi = hd f2;
         j = sj - 1;
         dsj = ds !! sj;
         mui = mus !! i;
         c = floor_ceil_num_denom (mui !! j) dsj
      in (if c = 0 then 
          basis_reduction_add_rows_loop n state i j fjs
         else  
             let muj = mus !! j in 
           basis_reduction_add_rows_loop n
                ((f1,  vec n (\<lambda> i. fi $ i - c * fj $ i) # tl f2), iarray_update mus i 
             (IArray.of_fun (\<lambda> jj. let mu = mui !! jj in 
                  if jj < j then mu - c * muj !! jj else 
                  if jj = j then mu - dsj * c else mu) i),
                  ds) i j fjs))"
proof -
  obtain f1 f2 mus ds where state: "state = ((f1,f2),mus, ds)" by (cases state, auto)
  show ?thesis unfolding basis_reduction_add_rows_loop.simps Let_def 
     state split dmu_ij_state.simps fi_state.simps get_nth_i_def update_i_def upd_fi_mu_state.simps
     d_state.simps
    by simp
qed

lemmas basis_reduction_add_rows_loop_code_equations =
  basis_reduction_add_rows_loop.simps(1) basis_reduction_add_rows_loop_code

declare basis_reduction_add_rows_loop_code_equations[code]


definition basis_reduction_add_rows where
  "basis_reduction_add_rows n upw i state = 
     (if upw 
        then basis_reduction_add_rows_loop n state i i (small_fs_state state) 
        else state)" 

context
  fixes \<alpha> :: rat and n m :: nat and fs_init :: "int vec list" 
begin

definition swap_mu :: "int iarray iarray \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int iarray iarray" where
  "swap_mu dmu i dmu_i_im1 dim1 di dsi = (let im1 = i - 1 in 
       IArray.of_fun (\<lambda> ii. if ii < im1 then dmu !! ii else 
       if ii > i then let dmu_ii = dmu !! ii in 
           IArray.of_fun (\<lambda> j. let dmu_ii_j = dmu_ii !! j in 
               if j = i then (dsi * dmu_ii !! im1 - dmu_i_im1 * dmu_ii_j) div di
               else if j = im1 then (dmu_i_im1 * dmu_ii_j + dmu_ii !! i * dim1) div di
               else dmu_ii_j) ii else 
       if ii = i then let mu_im1 = dmu !! im1 in 
           IArray.of_fun (\<lambda> j. if j = im1 then dmu_i_im1 else mu_im1 !! j) ii 
         else IArray.of_fun (\<lambda> j. dmu !! i !! j) ii) \<comment> \<open>ii = i - 1\<close>
       m)" 

definition basis_reduction_swap where
  "basis_reduction_swap i state = (let 
       di = d_state state i;
       dsi = d_state state (Suc i);
       dim1 = d_state state (i - 1);
       fi = fi_state state;
       fim1 = fim1_state state;
       dmu_i_im1 = dmu_ij_state state i (i - 1);
       fi' = fim1;
       fim1' = fi
     in (case state of (f,dmus,djs) \<Rightarrow>
         (False, i - 1, 
           (dec_i (update_im1 (update_i f fi') fim1'), 
            swap_mu dmus i dmu_i_im1 dim1 di dsi, 
            iarray_update djs i ((dsi * dim1 + dmu_i_im1 * dmu_i_im1) div di)))))"

text \<open>More efficient code which breaks abstraction of state.\<close>

lemma basis_reduction_swap_code[code]:
  "basis_reduction_swap i ((f1,f2), dmus, ds) = (let 
       di = ds !! i;
       dsi = ds !! (Suc i);
       im1 = i - 1;
       dim1 = ds !! im1;
       fi = hd f2;
       fim1 = hd f1;
       dmu_i_im1 = dmus !! i !! im1;
       fi' = fim1;
       fim1' = fi
     in (False, im1, 
           ((tl f1,fim1' # fi' # tl f2), 
            swap_mu dmus i dmu_i_im1 dim1 di dsi, 
            iarray_update ds i ((dsi * dim1 + dmu_i_im1 * dmu_i_im1) div di))))"
proof - 
  show ?thesis unfolding basis_reduction_swap_def split Let_def fi_state.simps fim1_state.simps 
    d_state.simps get_nth_im1_def get_nth_i_def update_i_def update_im1_def dec_i_def
    by simp
qed

definition basis_reduction_step where
  "basis_reduction_step upw i state = (if i = 0 then (True, Suc i, inc_state state)
     else let 
       state' = basis_reduction_add_rows n upw i state;
       di = d_state state' i;
       dsi = d_state state' (Suc i);
       dim1 = d_state state' (i - 1);
       (num,denom) = quotient_of \<alpha>
    in if di * di * denom \<le> num * dim1 * dsi then
          (True, Suc i, inc_state state') 
        else basis_reduction_swap i state')" 

partial_function (tailrec) basis_reduction_main where
  [code]: "basis_reduction_main upw i state = (if i < m
     then case basis_reduction_step upw i state of (upw',i',state') \<Rightarrow> 
       basis_reduction_main upw' i' state' else
       state)"

definition "initial_state = (let
  dmus = d\<mu>_impl fs_init;
  ds = IArray.of_fun (\<lambda> i. if i = 0 then 1 else let i1 = i - 1 in dmus !! i1 !! i1) (Suc m);
  dmus' = IArray.of_fun (\<lambda> i. let row_i = dmus !! i in
       IArray.of_fun (\<lambda> j. row_i !! j) i) m
  in (([], fs_init), dmus', ds) :: LLL_dmu_d_state)" 

end

definition "basis_reduction \<alpha> n fs = (let m = length fs in 
  basis_reduction_main \<alpha> n m True 0 (initial_state m fs))" 

definition "reduce_basis \<alpha> fs = (case fs of Nil \<Rightarrow> fs | Cons f _ \<Rightarrow> fs_state (basis_reduction \<alpha> (dim_vec f) fs))" 

definition "short_vector \<alpha> fs = hd (reduce_basis \<alpha> fs)"

lemma map_rev_Suc: "map f (rev [0..<Suc j]) = f j # map f (rev [0..< j])" by simp

context LLL
begin

definition mu_repr :: "int iarray iarray \<Rightarrow> int vec list \<Rightarrow> bool" where
  "mu_repr mu fs = (mu = IArray.of_fun (\<lambda> i. IArray.of_fun (d\<mu> fs i) i) m)" 

definition d_repr :: "int iarray \<Rightarrow> int vec list \<Rightarrow> bool" where
  "d_repr ds fs = (ds = IArray.of_fun (d fs) (Suc m))" 

fun LLL_impl_inv :: "LLL_dmu_d_state \<Rightarrow> nat \<Rightarrow> int vec list \<Rightarrow> bool" where
  "LLL_impl_inv (f,mu,ds) i fs = (list_repr i f (map (\<lambda> j. fs ! j) [0..<m])
    \<and> d_repr ds fs
    \<and> mu_repr mu fs)" 

context fixes state i fs upw f mu ds
  assumes impl: "LLL_impl_inv state i fs"
  and inv: "LLL_invariant upw i fs" 
  and state: "state = (f,mu,ds)" 
begin
lemma to_list_repr: "list_repr i f (map ((!) fs) [0..<m])"
  using impl[unfolded state] by auto

lemma to_mu_repr: "mu_repr mu fs" using impl[unfolded state] by auto
lemma to_d_repr: "d_repr ds fs" using impl[unfolded state] by auto

lemma dmu_ij_state: assumes j: "j < ii" 
  and ii: "ii < m" 
shows "dmu_ij_state state ii j = d\<mu> fs ii j" 
  unfolding to_mu_repr[unfolded mu_repr_def] state using ii j by auto

lemma fi_state: "i < m \<Longrightarrow> fi_state state = fs ! i"
  using get_nth_i[OF to_list_repr(1)] unfolding state by auto

lemma fim1_state: "i < m \<Longrightarrow> i \<noteq> 0 \<Longrightarrow> fim1_state state = fs ! (i - 1)"
  using get_nth_im1[OF to_list_repr(1)] unfolding state by auto

lemma d_state: "ii \<le> m \<Longrightarrow> d_state state ii = d fs ii"
  using to_d_repr[unfolded d_repr_def] state 
  unfolding state by (auto simp: nth_append)

lemma fs_state: "length fs = m \<Longrightarrow> fs_state state = fs"
  using of_list_repr[OF to_list_repr(1)] unfolding state by (auto simp: o_def intro!: nth_equalityI)

lemma LLL_state_inc_state: assumes i: "i < m"
shows "LLL_impl_inv (inc_state state) (Suc i) fs" 
  "fs_state (inc_state state) = fs_state state" 
proof -
  from LLL_invD[OF inv] have len: "length fs = m" by auto
  note inc = inc_i[OF to_list_repr(1)] 
  from inc i impl show "LLL_impl_inv (inc_state state) (Suc i) fs" 
    unfolding state by auto
  from of_list_repr[OF inc(1)] of_list_repr[OF to_list_repr(1)] i
  show "fs_state (inc_state state) = fs_state state" unfolding state by auto
qed
end
end

context LLL_with_assms
begin
lemma basis_reduction_add_rows_loop: assumes
    impl: "LLL_impl_inv state i fs" 
  and inv: "LLL_invariant True i fs" 
  and mu_small: "\<mu>_small_row i fs j"
  and res: "basis_reduction_add_rows_loop n state i j 
    (map ((!) fs) (rev [0 ..< j])) = state'" 
    (is "basis_reduction_add_rows_loop n state i j (?mapf fs j) = _")
  and j: "j \<le> i" 
  and i: "i < m" 
  and fs': "fs' = fs_state state'" 
shows 
  "LLL_impl_inv state' i fs'" 
  "LLL_invariant False i fs'" 
  "LLL_measure i fs' = LLL_measure i fs" 
proof (atomize(full), insert assms(1-6), induct j arbitrary: fs state)
  case (0 fs state)
  from LLL_invD[OF 0(2)] have len: "length fs = m" by auto
  from fs_state[OF 0(1-2) _ len] have "fs_state state = fs" by (cases state, auto)
  thus ?case using 0 basis_reduction_add_row_done[of i fs] i fs' by auto
next
  case (Suc j fs state)
  hence j: "j < i" and jj: "j \<le> i" and id: "(j < i) = True" by auto
  obtain f mu ds where state: "state = (f,mu,ds)" by (cases state, auto)
  note Linv = Suc(3)
  note inv = LLL_invD[OF Linv]
  note impl = Suc(2)
  from fi_state[OF impl Linv state i] have fi: "fi_state state = fs ! i" by auto
  have id: "Suc j - 1 = j" by simp
  note mu = dmu_ij_state[OF impl Linv state j i]
  let ?c = "floor_ceil (\<mu> fs i j)" 
  note floor = floor_ceil_num_denom_d\<mu>_d[OF LLL_invariant_fs_int[OF Linv] jj i]
  from LLL_d_pos[OF Linv] j i have dj: "d fs (Suc j) > 0" by auto
  note updates = d_d\<mu>_add_row[OF Linv i j refl refl Suc(4)]
  note d_state = d_state[OF impl Linv state]
  from d_state[of "Suc j"] j i have djs: "d_state state (Suc j) = d fs (Suc j)" by auto
  note res = Suc(5)[unfolded floor map_rev_Suc djs append.simps basis_reduction_add_rows_loop.simps 
      fi Let_def mu id int_times_rat_def]
  show ?case
  proof (cases "?c = 0")
    case True
    from res[unfolded True] 
    have res: "basis_reduction_add_rows_loop n state i j (?mapf fs j) = state'" 
      by simp
    note step = Linv basis_reduction_add_row_main_0[OF Linv i j True Suc(4)]
    show ?thesis using Suc(1)[OF impl step(1-2) res _ i] j by auto
  next
    case False
    hence id: "(?c = 0) = False" by auto
    from i j have jm: "j < m" by auto
    have idd: "vec n (\<lambda>ia. fs ! i $v ia - ?c * fs ! j $v ia) = 
      fs ! i - ?c \<cdot>\<^sub>v fs ! j" 
      by (intro eq_vecI, insert inv(4)[OF i] inv(4)[OF jm], auto)
    define fi' where "fi' = fs ! i - ?c \<cdot>\<^sub>v fs ! j" 
    obtain fs'' where fs'': "fs[i := fs ! i - ?c \<cdot>\<^sub>v fs ! j] = fs''" by auto
    note step = basis_reduction_add_row_main[OF Linv i j refl fs''[symmetric] Suc(4)]
    note updates = updates[unfolded fs'']
    have map_id_f: "?mapf fs j = ?mapf fs'' j"  
      by (rule nth_equalityI, insert j i, auto simp: rev_nth fs''[symmetric])
    have nth_id: "[0..<m] ! i = i" using i by auto
    note res = res[unfolded False map_id_f id if_False idd]
    have fi: "fi' = fs'' ! i" unfolding fs''[symmetric] fi'_def using inv(6) i by auto
    let ?fn = "\<lambda> fs i. (fs ! i, sq_norm (gso fs i))" 
    let ?d = "\<lambda> fs i. d fs (Suc i)" 
    let ?mu' = "IArray.of_fun
       (\<lambda>jj. if jj < j then dmu_ij_state state i jj - ?c * dmu_ij_state state j jj
             else if jj = j then dmu_ij_state state i jj - ?d fs j * ?c else dmu_ij_state state i jj) i" 
    have mu': "?mu' = IArray.of_fun (d\<mu> fs'' i) i" (is "_ = ?mu'i")
    proof (rule iarray_cong', goal_cases)
      case (1 jj)
      from 1 j i have jm: "j < m" by auto
      show ?case unfolding dmu_ij_state[OF impl Linv state 1 i] using dmu_ij_state[OF impl Linv state _ jm]
        by (subst updates(2)[OF i 1], auto)
    qed
    {
      fix ii
      assume ii: "ii < m" "ii \<noteq> i" 
      hence "(IArray.of_fun (\<lambda>i. IArray.of_fun (d\<mu> fs i) i) m) !! ii
        = IArray.of_fun (d\<mu> fs ii) ii" by auto
      also have "\<dots> = IArray.of_fun (d\<mu> fs'' ii) ii" 
      proof (rule iarray_cong', goal_cases)
        case (1 j)
        with ii have j: "Suc j \<le> m" by auto
        show ?case unfolding updates(2)[OF ii(1) 1] using ii by auto
      qed
      finally have "(IArray.of_fun (\<lambda>i. IArray.of_fun (d\<mu> fs i) i) m) !! ii 
         = IArray.of_fun (d\<mu> fs'' ii) ii" by auto
    } note ii = this
    let ?mu'' = "iarray_update mu i (IArray.of_fun (d\<mu> fs'' i) i)" 
    have new_array: "?mu'' = IArray.of_fun (\<lambda> i. IArray.of_fun (d\<mu> fs'' i) i) m" 
      unfolding iarray_update_of_fun to_mu_repr[OF impl Linv state, unfolded mu_repr_def]
      by (rule iarray_cong', insert ii, auto)
    have d': "(map (?d fs) (rev [0..<j])) = (map (?d fs'') (rev [0..<j]))" 
      by (rule nth_equalityI, force, intro allI impI, simp, subst updates(1), insert j i, auto
        simp: nth_rev)
    have repr_id:
      "map ((!) fs) [0..<m][i := (fs'' ! i)] = map ((!) fs'') [0..<m]" (is "?xs = ?ys")
    proof (rule nth_equalityI, force, intro allI impI)
      fix j
      assume "j < length ?xs" 
      thus "?xs ! j = ?ys ! j" unfolding fs''[symmetric] i by (cases "j = i", auto)
    qed
    have repr_id_d: 
      "map (d fs) [0..<Suc m] = map (d fs'') [0..<Suc m]"
      by (rule nth_equalityI, force, intro allI impI, insert step(4,6), auto simp: nth_append)
    have mu: "fs ! i - ?c \<cdot>\<^sub>v fs ! j = fs'' ! i" unfolding fs''[symmetric] using inv(6) i by auto
    note res = res[unfolded mu' mu d']
    show ?thesis unfolding step(3)[symmetric]
    proof (rule Suc(1)[OF _ step(1,2) res _ i])
      note list_repr = to_list_repr[OF impl Linv state]
      from i have ii: "i < length [0..<m]" by auto
      show "LLL_impl_inv (upd_fi_mu_state state i (fs'' ! i) ?mu'i) i fs''" 
        unfolding upd_fi_mu_state.simps state LLL_impl_inv.simps new_array
      proof (intro conjI)
        show "list_repr i (update_i f (fs'' ! i)) (map ((!) fs'') [0..<m])" 
          using update_i[OF list_repr(1), unfolded length_map, OF ii] unfolding repr_id[symmetric] .
        show "d_repr ds fs''" unfolding to_d_repr[OF impl Linv state, unfolded d_repr_def] d_repr_def
          by (rule iarray_cong', subst step(6), auto)
      qed (auto simp: mu_repr_def)
    qed (insert i j, auto)
  qed
qed

lemma basis_reduction_add_rows: assumes
     impl: "LLL_impl_inv state i fs" 
  and inv: "LLL_invariant upw i fs" 
  and res: "basis_reduction_add_rows n upw i state = state'" 
  and i: "i < m" 
  and fs': "fs' = fs_state state'" 
shows 
  "LLL_impl_inv state' i fs'" 
  "LLL_invariant False i fs'" 
  "LLL_measure i fs' = LLL_measure i fs" 
proof (atomize(full), goal_cases)
  case 1
  obtain f mu ds where state: "state = (f,mu,ds)" by (cases state, auto)
  note def = basis_reduction_add_rows_def
  show ?case
  proof (cases upw)
    case False
    from LLL_invD[OF inv] have len: "length fs = m" by auto
    from fs_state[OF impl inv state len] have "fs_state state = fs" by auto
    with assms False show ?thesis by (auto simp: def)
  next
    case True
    with inv have "LLL_invariant True i fs" by auto
    note start = this \<mu>_small_row_refl[of i fs]
    have id: "small_fs_state state = map (\<lambda> i. fs ! i) (rev [0..<i])"
      unfolding state using to_list_repr[OF impl inv state] i
      unfolding list_repr_def by (auto intro!: nth_equalityI simp: nth_rev min_def)
    from i have mm: "[0..<m] = [0 ..< i] @ [i] @ [Suc i ..< m]"
      by (intro nth_equalityI, auto simp: nth_append nth_Cons split: nat.splits)
    from res[unfolded def] True 
    have "basis_reduction_add_rows_loop n state i i (small_fs_state state) = state'" by auto
    from basis_reduction_add_rows_loop[OF impl start(1-2) this[unfolded id] le_refl i fs']
    show ?thesis by auto
  qed
qed

lemma basis_reduction_swap: assumes 
  impl: "LLL_impl_inv state i fs" 
  and inv: "LLL_invariant False i fs" 
  and res: "basis_reduction_swap m i state = (upw',i',state')" 
  and cond: "sq_norm (gso fs (i - 1)) > \<alpha> * sq_norm (gso fs i)" 
  and i: "i < m" and i0: "i \<noteq> 0" 
  and fs': "fs' = fs_state state'" 
shows 
  "LLL_impl_inv state' i' fs'" (is ?g1)
  "LLL_invariant upw' i' fs'" (is ?g2)
  "LLL_measure i' fs' < LLL_measure i fs" (is ?g3)
proof -
  from i i0 have ii: "i - 1 < i" and le_m: "i - 1 \<le> m" "i \<le> m" "Suc i \<le> m" by auto
  obtain f mu ds where state: "state = (f,mu,ds)" by (cases state, auto)
  note dmu_ij_state = dmu_ij_state[OF impl inv state]
  note d_state = d_state[OF impl inv state]
  note res = res[unfolded basis_reduction_swap_def Let_def split state, folded state,
    unfolded fi_state[OF impl inv state i] fim1_state[OF impl inv state i i0]] 
  note state_id = dmu_ij_state[OF ii i] 
  note d_state_i = d_state[OF le_m(1)] d_state[OF le_m(2)] d_state[OF le_m(3)]
  from LLL_invD[OF inv] have len: "length fs = m" by auto
  from fs_state[OF impl inv state len] have fs: "fs_state state = fs" by auto
  obtain fs'' where fs'': "fs[i := fs ! (i - 1), i - 1 := fs ! i] = fs''" by auto
  let ?r = rat_of_int
  let ?d = "d fs" 
  let ?d' = "d fs''" 
  let ?dmus = "dmu_ij_state state" 
  let ?ds = "d_state state" 
  note swap = basis_reduction_swap[OF inv i i0 cond refl, unfolded fs'']
  note dmu = d\<mu>[OF LLL_invariant_fs_int[OF inv]]
  note dmu' = d\<mu>[OF LLL_invariant_fs_int[OF swap(1)]]
  note inv' = LLL_invD[OF inv]
  have fi: "fs ! (i - 1) = fs'' ! i" "fs ! i = fs'' ! (i - 1)" 
    unfolding fs''[symmetric] using inv'(6) i i0 by auto
  from res have upw': "upw' = False" "i' = i - 1" by auto
  let ?dmu_repr' = "swap_mu m mu i (?dmus i (i - 1)) (?d (i - 1)) (?d i) (?d (Suc i))" 
  let ?d'i = "(?d (Suc i) * ?d (i - 1) + ?dmus i (i - 1) * ?dmus i (i - 1)) div (?d i)" 
  from res[unfolded fi d_state_i] 
  have res: "upw' = False" "i' = i - 1" 
    "state' = (dec_i (update_im1 (update_i f (fs'' ! i)) (fs'' ! (i - 1))), 
       ?dmu_repr', iarray_update ds i ?d'i)" by auto 
  from i have ii: "i < length [0..<m]" and im1: "i - 1 < m" by auto
  note list_repr = to_list_repr[OF impl inv state]
  from dec_i[OF update_im1[OF update_i[OF list_repr(1)]], unfolded length_map, OF ii i0 i0]
  have 
    "list_repr (i - 1) (dec_i (update_im1 (update_i f (fs'' ! i)) (fs'' ! (i - 1)))) (map ((!) fs) [0..<m][i := (fs'' ! i), 
       i - 1 := (fs'' ! (i - 1))])" (is "list_repr _ ?fr ?xs") .
  also have "?xs = map ((!) fs'') [0..<m]" unfolding fs''[symmetric]
    by (intro nth_equalityI, insert i i0 len, auto simp: nth_append, rename_tac ii, case_tac "ii \<in> {i-1,i}", auto)
  finally have f_repr: "list_repr (i - 1) ?fr (map ((!) fs'') [0..<m])" .    
  from i0 have sim1: "Suc (i - 1) = i" by simp
  from LLL_d_Suc[OF inv im1, unfolded sim1] 
  have "length fs'' = m" 
    using fs'' inv'(6) by auto
  hence fs_id: "fs' = fs''" unfolding fs' res fs_state.simps using of_list_repr[OF f_repr] 
    by (intro nth_equalityI, auto simp: o_def)
  from to_mu_repr[OF impl inv state] have mu: "mu_repr mu fs" by auto
  from to_d_repr[OF impl inv state] have d_repr: "d_repr ds fs" by auto
  note mu_def = mu[unfolded mu_repr_def]
  note updates = d_d\<mu>_swap[OF inv i i0 cond fs''[symmetric]]
  note dmu_ii = dmu_ij_state[OF \<open>i - 1 < i\<close> i]
  show ?g1 unfolding fs_id LLL_impl_inv.simps res
  proof (intro conjI f_repr)
    show "d_repr (iarray_update ds i ?d'i) fs''" 
      unfolding d_repr[unfolded d_repr_def] d_repr_def iarray_update_of_fun dmu_ii
      by (rule iarray_cong', subst updates(1), auto simp: nth_append intro: arg_cong)
    show "mu_repr ?dmu_repr' fs''" unfolding mu_repr_def swap_mu_def Let_def dmu_ii 
    proof (rule iarray_cong', goal_cases)
      case ii: (1 ii) 
      show ?case
      proof (cases "ii < i - 1")
        case small: True
        hence id: "(ii = i) = False" "(ii = i - 1) = False" "(i < ii) = False" "(ii < i - 1) = True" by auto
        have mu: "mu !! ii = IArray.of_fun (d\<mu> fs ii) ii" 
          using ii unfolding mu_def by auto
        show ?thesis unfolding id if_True if_False mu
          by (rule iarray_cong', insert small ii i i0, subst updates(2), simp_all, linarith) 
      next
        case False
        hence iFalse: "(ii < i - 1) = False" by auto
        show ?thesis unfolding iFalse if_False if_distrib[of "\<lambda> f. IArray.of_fun f ii", symmetric]
          dmu_ij_state.simps[of f mu ds, folded state, symmetric] 
        proof (rule iarray_cong', goal_cases)
          case j: (1 j)
          note upd = updates(2)[OF ii j] dmu_ii dmu_ij_state[OF j ii] if_distrib[of "\<lambda> x. x j"]
          note simps = dmu_ij_state[OF _ ii] dmu_ij_state[OF _ im1] dmu_ij_state[OF _ i]
          from False consider (I) "ii = i" "j = i - 1" | (Is) "ii = i" "j \<noteq> i - 1" | 
            (Im1) "ii = i - 1" | (large) "ii > i" by linarith
          thus ?case 
          proof (cases)
            case (I)
            show ?thesis unfolding upd using I by auto
          next
            case (Is)
            show ?thesis unfolding upd using Is j simps by auto
          next
            case (Im1)
            hence id: "(i < ii) = False" "(ii = i) = False" "(ii = i - 1) = True" using i0 by auto
            show ?thesis unfolding upd unfolding id if_False if_True by (rule simps, insert j Im1, auto)
          next
            case (large)
            hence "i - 1 < ii" "i < ii" by auto
            note simps = simps(1)[OF this(1)] simps(1)[OF this(2)]
            from large have id: "(i < ii) = True" "(ii = i - 1) = False" "\<And> x. (ii = i \<and> x) = False" by auto
            show ?thesis unfolding id if_True if_False upd simps by auto
          qed
        qed
      qed
    qed
  qed
  from swap(1-2) fs_id show ?g2 ?g3 using res by auto
qed

lemma basis_reduction_step: assumes 
  impl: "LLL_impl_inv state i fs" 
  and inv: "LLL_invariant upw i fs" 
  and res: "basis_reduction_step \<alpha> n m upw i state = (upw',i',state')" 
  and i: "i < m" 
  and fs': "fs' = fs_state state'" 
shows 
  "LLL_impl_inv state' i' fs'" 
  "LLL_invariant upw' i' fs'" 
  "LLL_measure i' fs' < LLL_measure i fs" 
proof (atomize(full), goal_cases)
  case 1
  obtain f mu ds where state: "state = (f,mu,ds)" by (cases state, auto)
  note def = basis_reduction_step_def
  from LLL_invD[OF inv] have len: "length fs = m" by auto
  from fs_state[OF impl inv state len] have fs: "fs_state state = fs" by auto
  show ?case
  proof (cases "i = 0")
    case True
    from LLL_state_inc_state[OF impl inv state i] i
      assms increase_i[OF inv i True] True 
      res fs' fs
    show ?thesis by (auto simp: def)
  next
    case False
    hence id: "(i = 0) = False" by auto
    obtain state'' where state'': "basis_reduction_add_rows n upw i state = state''" by auto
    define fs'' where fs'': "fs'' = fs_state state''" 
    obtain f mu ds where state: "state'' = (f,mu,ds)" by (cases state'', auto)
    from basis_reduction_add_rows[OF impl inv state'' i fs'']
    have inv: "LLL_invariant False i fs''"
      and meas: "LLL_measure i fs = LLL_measure i fs''" 
      and impl: "LLL_impl_inv state'' i fs''" by auto
    obtain num denom where quot: "quotient_of \<alpha> = (num,denom)" by force
    note d_state = d_state[OF impl inv state]
    from i have le: "i - 1 \<le> m" " i \<le> m" "Suc i \<le> m" by auto
    note d_state = d_state[OF le(1)] d_state[OF le(2)] d_state[OF le(3)]
    note res = res[unfolded def id if_False Let_def state'' quot split d_state 
        d_sq_norm_comparison[OF LLL_invariant_fs_int[OF inv] quot i False]] 
    note pos = LLL_d_pos[OF inv le(1)] LLL_d_pos[OF inv le(2)] quotient_of_denom_pos[OF quot]
    from False have sim1: "Suc (i - 1) = i" by simp
    let ?r = "rat_of_int" 
    let ?x = "sq_norm (gso fs'' (i - 1))" 
    let ?y = "\<alpha> * sq_norm (gso fs'' i)" 
    show ?thesis
    proof (cases "?x \<le> ?y")
      case True
      from increase_i[OF inv i _ True] True res meas LLL_state_inc_state[OF impl inv state i] fs' fs''
      show ?thesis by auto
    next
      case gt: False
      hence gt: "?x > ?y" and id: "(?x \<le> ?y) = False" by auto
      from res[unfolded id if_False] have "basis_reduction_swap m i state'' = (upw', i', state')" by auto
      from basis_reduction_swap[OF impl inv this gt i False fs'] show ?thesis using meas by auto
    qed
  qed
qed

lemma basis_reduction_main: assumes 
  impl: "LLL_impl_inv state i fs" 
  and inv: "LLL_invariant upw i fs" 
  and res: "basis_reduction_main \<alpha> n m upw i state = state'" 
  and fs': "fs' = fs_state state'" 
shows "LLL_invariant True m fs'" 
      "LLL_impl_inv state' m fs'" 
proof (atomize(full), insert assms(1-3), induct "LLL_measure i fs" arbitrary: i fs upw state rule: less_induct)
  case (less i fs upw)
  have id: "LLL_invariant upw i fs = True" using less by auto
  note res = less(4)[unfolded basis_reduction_main.simps[of _ _ _ upw]]
  note inv = less(3)
  note impl = less(2)
  note IH = less(1)
  show ?case
  proof (cases "i < m")
    case i: True
    obtain i'' state'' upw'' where step: "basis_reduction_step \<alpha> n m upw i state = (upw'',i'',state'')" 
      (is "?step = _") by (cases ?step, auto)
    with res i have res: "basis_reduction_main \<alpha> n m upw'' i'' state'' = state'" by auto
    note main = basis_reduction_step[OF impl inv step i refl]
    from IH[OF main(3,1,2) res]
    show ?thesis by auto
  next
    case False
    from LLL_invD[OF inv] have len: "length fs = m" by auto
    obtain f mu ds where state: "state = (f,mu,ds)" by (cases state, auto)
    from fs_state[OF impl inv state len] have fs: "fs_state state = fs" by auto
    from False LLL_invD[OF inv] have i: "i = m" upw by auto
    with False res inv impl fs show ?thesis by (auto simp: fs')
  qed
qed

lemma initial_state: "LLL_impl_inv (initial_state m fs_init) 0 fs_init" 
proof -
  have f_repr: "list_repr 0 ([], fs_init) (map ((!) fs_init) [0..<m])" 
    unfolding list_repr_def by (simp, intro nth_equalityI, auto simp: len)
  from fs_init have Rn: "set (RAT fs_init) \<subseteq> Rn" by auto
  have 1: "1 = d fs_init 0" unfolding d_def by simp
  define j where "j = m" 
  have jm: "j \<le> m" unfolding j_def by auto
  have 0: "0 = m - j" unfolding j_def by auto
  have mu_repr: "mu_repr (IArray.of_fun (\<lambda>i. IArray.of_fun ((!!) (d\<mu>_impl fs_init !! i)) i) m) fs_init" 
    unfolding d\<mu>_impl[OF lin_dep len] mu_repr_def 
    by (intro iarray_cong', simp only: of_fun_nth)
  have d_repr: "d_repr (IArray.of_fun (\<lambda>i. if i = 0 then 1 else d\<mu>_impl fs_init !! (i - 1) !! (i - 1)) (Suc m)) fs_init" 
    unfolding d\<mu>_impl[OF lin_dep len] d_repr_def 
  proof (intro iarray_cong', goal_cases)
    case (1 i)
    show ?case
    proof (cases "i = 0")
      case False
      hence le: "i - 1 < m" "i - 1 < i" and id: "(i = 0) = False" "Suc (i - 1) = i" using 1 by auto
      show ?thesis unfolding of_fun_nth[OF le(1)] of_fun_nth[OF le(2)] id if_False d\<mu>_def 
        by (simp add: gs.\<mu>.simps)
    next
      case True
      have "d fs_init 0 = 1" unfolding d_def gs.Gramian_determinant_0 by simp
      thus ?thesis unfolding True by simp
    qed 
  qed 
  show ?thesis unfolding initial_state_def Let_def LLL_impl_inv.simps id
    by (intro conjI f_repr mu_repr d_repr)
qed

lemma basis_reduction: assumes res: "basis_reduction \<alpha> n fs_init = state" 
  and fs: "fs = fs_state state" 
shows "LLL_invariant True m fs" 
  "LLL_impl_inv state m fs" 
  using basis_reduction_main[OF initial_state LLL_inv_initial_state res[unfolded basis_reduction_def len Let_def] fs]
  by auto

lemma reduce_basis: assumes res: "reduce_basis \<alpha> fs_init = fs" 
  shows "gs.reduced \<alpha> m (map (gso fs) [0..<m]) (\<mu> fs)" "LLL_invariant True m fs" 
proof -
  show "LLL_invariant True m fs" 
  proof (cases fs_init)
    case (Cons f)
    from fs_init[unfolded Cons] have "dim_vec f = n" by auto
    from res[unfolded reduce_basis_def Cons list.simps this, folded Cons]
    have "fs_state (basis_reduction \<alpha> n fs_init) = fs" by auto
    from basis_reduction(1)[OF refl refl, unfolded this] show "LLL_invariant True m fs" .
  next
    case Nil
    with len have m0: "m = 0" by auto
    from Nil res have fs: "fs = fs_init" unfolding reduce_basis_def by auto
    show "LLL_invariant True m fs" unfolding fs LLL_invariant_def L_def gs.reduced_def gs.weakly_reduced_def 
      using lin_dep unfolding m0 Nil by auto
  qed
  thus "gs.reduced \<alpha> m (map (gso fs) [0..<m]) (\<mu> fs)" by (rule LLL_inv_m_imp_reduced)
qed

lemma short_vector: assumes res: "short_vector \<alpha> fs_init = v"
  and m0: "m \<noteq> 0"
shows "v \<in> carrier_vec n"
  "v \<in> L - {0\<^sub>v n}"  
  "h \<in> L - {0\<^sub>v n} \<Longrightarrow> rat_of_int (sq_norm v) \<le> \<alpha> ^ (m - 1) * rat_of_int (sq_norm h)" 
  "v \<noteq> 0\<^sub>v j" 
  using basis_reduction_short_vector[OF reduce_basis(2)[OF refl] res[symmetric, unfolded short_vector_def] m0] 
  by blast+

end
end