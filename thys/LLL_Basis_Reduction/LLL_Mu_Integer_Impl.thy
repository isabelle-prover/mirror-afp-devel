(*
    Authors:    René Thiemann
    License:    BSD
*)
subsection \<open>LLL Implementation which Stores Multiples of the $\mu$-values and the Norms of the GSO as Integers\<close>

theory LLL_Mu_Integer_Impl
  imports LLL
   List_Representation
   LLL_Number_Bounds
begin

text \<open>We store the $f$, $\mu$, and $||g||^2$ values.\<close>

definition iarray_update :: "'a iarray \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a iarray" where
  "iarray_update a i x = IArray.of_fun (\<lambda> j. if j = i then x else IArray.sub a j) (IArray.length a)" 

lemma iarray_of_fun_cong: "(\<And> i. i < n \<Longrightarrow> f i = g i) \<Longrightarrow> IArray.of_fun f n = IArray.of_fun g n" 
  unfolding IArray.of_fun_def by auto

lemma iarray_length_of_fun[simp]: "IArray.length (IArray.of_fun f n) = n" by simp

lemma division_to_div: "rat_of_int x = of_int y / of_int z \<Longrightarrow> x = y div z" 
  by (metis floor_divide_of_int_eq floor_of_int)

hide_fact Word.inc_i

type_synonym LLL_gso_state = "int vec list_repr \<times> int iarray iarray \<times> int iarray"

fun fi_state :: "LLL_gso_state \<Rightarrow> int vec" where
  "fi_state (f,mu,d) = get_nth_i f" 

fun fim1_state :: "LLL_gso_state \<Rightarrow> int vec" where
  "fim1_state (f,mu,d) = get_nth_im1 f" 

fun d_state :: "LLL_gso_state \<Rightarrow> nat \<Rightarrow> int" where
  "d_state (f,mu,d) i = IArray.sub d i" 

fun fs_state :: "LLL_gso_state \<Rightarrow> int vec list" where
  "fs_state (f,mu,d) = of_list_repr f" 

fun upd_fi_mu_state :: "LLL_gso_state \<Rightarrow> nat \<Rightarrow> int vec \<Rightarrow> int iarray \<Rightarrow> LLL_gso_state" where
  "upd_fi_mu_state (f,mu,d) i fi mu_i = (update_i f fi, iarray_update mu i mu_i,d)" 

fun small_fs_state :: "LLL_gso_state \<Rightarrow> int vec list" where
  "small_fs_state (f,_) = fst f" 

fun dmu_ij_state :: "LLL_gso_state \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int" where
  "dmu_ij_state (f,mu,_) i j = IArray.sub (IArray.sub mu i) j" 

fun inc_state :: "LLL_gso_state \<Rightarrow> LLL_gso_state" where
  "inc_state (f,mu,d) = (inc_i f, mu, d)" 

definition floor_ceil_num_denom :: "int \<Rightarrow> int \<Rightarrow> int" where
  "floor_ceil_num_denom n d = ((2 * n + d) div (2 * d))" 

lemma floor_ceil_num_denom: "denom > 0 \<Longrightarrow> floor_ceil_num_denom num denom = 
  floor_ceil (of_int num / rat_of_int denom)" 
  unfolding floor_ceil_def floor_ceil_num_denom_def
  unfolding floor_divide_of_int_eq[where ?'a = rat, symmetric]
  by (rule arg_cong[of _ _ floor], simp add: add_divide_distrib)

fun basis_reduction_add_rows_loop where
  "basis_reduction_add_rows_loop state i j [] = state" 
| "basis_reduction_add_rows_loop state i sj (fj # fjs) = (
     let fi = fi_state state;
         dsj = d_state state sj;
         j = sj - 1;
         c = floor_ceil_num_denom (dmu_ij_state state i j) dsj;
         state' = (if c = 0 then state else upd_fi_mu_state state i (fi - c \<cdot>\<^sub>v fj) 
             (IArray.of_fun (\<lambda> jj. let mu = dmu_ij_state state i jj in 
                  if jj < j then mu - c * dmu_ij_state state j jj else 
                  if jj = j then mu - dsj * c else mu) i))
      in basis_reduction_add_rows_loop state' i j fjs)"

text \<open>More efficient code which breaks abstraction of state.\<close>

lemma basis_reduction_add_rows_loop_code: 
  "basis_reduction_add_rows_loop state i sj (fj # fjs) = (
     case state of ((f1,f2),mus,ds) \<Rightarrow> 
     let fi = hd f2;
         j = sj - 1;
         dsj = IArray.sub ds sj;
         mui = IArray.sub (IArray.sub mus i);
         c = floor_ceil_num_denom (mui j) dsj
      in (if c = 0 then 
          basis_reduction_add_rows_loop state i j fjs
         else  
             let muj = IArray.sub (IArray.sub mus j) in 
           basis_reduction_add_rows_loop
                ((f1,  (fi - c \<cdot>\<^sub>v fj) # tl f2), iarray_update mus i 
             (IArray.of_fun (\<lambda> jj. let mu = mui jj in 
                  if jj < j then mu - c * muj jj else 
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
  "basis_reduction_add_rows upw i state = 
     (if upw 
        then basis_reduction_add_rows_loop state i i (small_fs_state state) 
        else state)" 

context
  fixes \<alpha> :: rat and n m :: nat and fs_init :: "int vec list" 
begin

definition swap_mu :: "int iarray iarray \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int iarray iarray" where
  "swap_mu dmu i dmu_i_im1 dim1 di dsi = (let im1 = i - 1 in 
       IArray.of_fun (\<lambda> ii. if ii < im1 then IArray.sub dmu ii else 
       if ii > i then let dmu_ii = IArray.sub (IArray.sub dmu ii) in 
           IArray.of_fun (\<lambda> j. let dmu_ii_j = dmu_ii j in 
               if j = i then (dsi * dmu_ii im1 - dmu_i_im1 * dmu_ii_j) div di
               else if j = im1 then (dmu_i_im1 * dmu_ii_j + dmu_ii i * dim1) div di
               else dmu_ii_j) ii else 
       if ii = i then let mu_im1 = IArray.sub (IArray.sub dmu im1) in 
           IArray.of_fun (\<lambda> j. if j = im1 then dmu_i_im1 else mu_im1 j) ii 
         else IArray.of_fun (IArray.sub (IArray.sub dmu i)) ii) \<comment> \<open>ii = i - 1\<close>
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
       di = IArray.sub ds i;
       dsi = IArray.sub ds (Suc i);
       im1 = i - 1;
       dim1 = IArray.sub ds im1;
       fi = hd f2;
       fim1 = hd f1;
       dmu_i_im1 = IArray.sub (IArray.sub dmus i) im1;
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
       state' = basis_reduction_add_rows upw i state;
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

fun norms_to_ds where 
    "norms_to_ds d [] = [d]" 
  | "norms_to_ds d (ni # nis) = (d # norms_to_ds (int_of_rat (int_times_rat d ni)) nis)" 

(* TODO: use better gram_schmidt, which already computes mu-values *)
definition "initial_state = (let
  (n_gs, mus) = norms_mus_rat n (map (map_vec rat_of_int) fs_init);
  ds = (IArray (norms_to_ds 1 n_gs) :: int iarray)
  in (([], fs_init), 
    IArray.of_fun (\<lambda> i. IArray.of_fun (\<lambda> j. int_of_rat (int_times_rat (IArray.sub ds (Suc j)) (mus ! i ! j))) i) m, 
    ds) :: LLL_gso_state)" 

end

definition "basis_reduction \<alpha> n fs = basis_reduction_main \<alpha> (length fs) True 0 (initial_state n (length fs) fs)" 

definition "reduce_basis \<alpha> fs = (case fs of Nil \<Rightarrow> fs | Cons f _ \<Rightarrow> fs_state (basis_reduction \<alpha> (dim_vec f) fs))" 

definition "short_vector \<alpha> fs = hd (reduce_basis \<alpha> fs)"

lemma map_rev_Suc: "map f (rev [0..<Suc j]) = f j # map f (rev [0..< j])" by simp

context LLL
begin

definition "d\<mu> fs i j = int_of_rat (of_int (d fs (Suc j)) * \<mu> fs i j)" 

definition mu_repr :: "int iarray iarray \<Rightarrow> int vec list \<Rightarrow> bool" where
  "mu_repr mu fs = (mu = IArray.of_fun (\<lambda> i. IArray.of_fun (d\<mu> fs i) i) m)" 

definition d_repr :: "int iarray \<Rightarrow> int vec list \<Rightarrow> bool" where
  "d_repr ds fs = (ds = IArray.of_fun (d fs) (Suc m))" 

fun LLL_impl_inv :: "LLL_gso_state \<Rightarrow> nat \<Rightarrow> int vec list \<Rightarrow> bool" where
  "LLL_impl_inv (f,mu,ds) i fs = (list_repr i f (map (\<lambda> j. fs ! j) [0..<m])
    \<and> d_repr ds fs
    \<and> mu_repr mu fs)" 

lemma d\<mu>: assumes inv: "LLL_invariant upw i fs" "j < ii" "ii < m" 
  shows "of_int (d\<mu> fs ii j) = of_int (d fs (Suc j)) * \<mu> fs ii j" 
  unfolding d\<mu>_def using LLL_mu_d_Z[OF inv] by auto

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
shows "of_int (dmu_ij_state state ii j) = of_int (d fs (Suc j)) * \<mu> fs ii j" 
  unfolding to_mu_repr[unfolded mu_repr_def] state using d\<mu>[OF inv assms] ii j by auto

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

lemma int_via_rat_eqI: "rat_of_int x = rat_of_int y \<Longrightarrow> x = y" by auto

context LLL_with_assms
begin
lemma basis_reduction_add_rows_loop: assumes
    impl: "LLL_impl_inv state i fs" 
  and inv: "LLL_invariant True i fs" 
  and mu_small: "\<mu>_small_row i fs j"
  and res: "basis_reduction_add_rows_loop state i j 
    (map ((!) fs) (rev [0 ..< j])) = state'" 
    (is "basis_reduction_add_rows_loop state i j (?mapf fs j) = _")
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
  hence j: "j < i" and id: "(j < i) = True" by auto
  obtain f mu ds where state: "state = (f,mu,ds)" by (cases state, auto)
  note Linv = Suc(3)
  note inv = LLL_invD[OF Linv]
  note impl = Suc(2)
  from fi_state[OF impl Linv state i] have fi: "fi_state state = fs ! i" by auto
  have id: "Suc j - 1 = j" by simp
  note mu = dmu_ij_state[OF impl Linv state j i]
  let ?c = "floor_ceil (\<mu> fs i j)" 
  from LLL_d_pos[OF Linv] j i have dj: "d fs (Suc j) > 0" by auto
  have fl_ceil: "floor_ceil_num_denom (dmu_ij_state state i j) (d fs (Suc j)) = ?c" 
    by (subst floor_ceil_num_denom, unfold mu, insert dj, auto)
  note d_state = d_state[OF impl Linv state]
  from d_state[of "Suc j"] j i have djs: "d_state state (Suc j) = d fs (Suc j)" by auto
  note res = Suc(5)[unfolded fl_ceil map_rev_Suc djs append.simps basis_reduction_add_rows_loop.simps 
      fi Let_def mu id int_times_rat_def]
  show ?case
  proof (cases "?c = 0")
    case True
    from res[unfolded True] 
    have res: "basis_reduction_add_rows_loop state i j (?mapf fs j) = state'" 
      by simp
    note step = Linv basis_reduction_add_row_main_0[OF Linv i j True Suc(4)]
    show ?thesis using Suc(1)[OF impl step(1-2) res _ i] j by auto
  next
    case False
    hence id: "(?c = 0) = False" by auto
    define fi' where "fi' = fs ! i - ?c \<cdot>\<^sub>v fs ! j" 
    obtain fs'' where fs'': "fs[i := fs ! i - ?c \<cdot>\<^sub>v fs ! j] = fs''" by auto
    note step = basis_reduction_add_row_main[OF Linv i j refl refl Suc(4), unfolded fs'']
    have map_id_f: "?mapf fs j = ?mapf fs'' j"  
      by (rule nth_equalityI, insert j step(4) i, auto simp: rev_nth fs''[symmetric])
    have nth_id: "[0..<m] ! i = i" using i by auto
    note res = res[unfolded False map_id_f id if_False]
    have fi: "fi' = fs'' ! i" unfolding fs''[symmetric] fi'_def using inv(7) i by auto
    let ?fn = "\<lambda> fs i. (fs ! i, sq_norm (gso fs i))" 
    have repr_id: "(map (?fn fs) [0..<m] [i := (fs'' ! i, \<parallel>gso fs'' i\<parallel>\<^sup>2)])
      = (map (?fn fs'') [0..<m])" (is "?xs = ?ys") 
    proof (rule nth_equalityI, force, intro allI impI)
      fix j
      assume "j < length ?xs" 
      thus "?xs ! j = ?ys ! j" 
        using step(4) unfolding fs''[symmetric] i 
        by (cases "j = i", auto)
    qed
    let ?d = "\<lambda> fs i. d fs (Suc i)" 
    let ?mu' = "IArray.of_fun
       (\<lambda>jj. if jj < j then dmu_ij_state state i jj - ?c * dmu_ij_state state j jj
             else if jj = j then dmu_ij_state state i jj - ?d fs j * ?c else dmu_ij_state state i jj) i" 
    have mu': "?mu' = IArray.of_fun (d\<mu> fs'' i) i" (is "_ = ?mu'i")
    proof (rule iarray_of_fun_cong, goal_cases)
      case (1 jj)
      let ?muu = "of_int (d fs'' (Suc jj)) * \<mu> fs'' i jj" 
      from 1 j i have jj: "jj \<le> i" and jm: "j < m" and jjm: "jj < m" by auto
      have id': "d fs'' (Suc jj) = d fs (Suc jj)" by (rule step(6), insert jjm, auto)
      define c where "c = ?c" 
      show ?case 
        by (rule int_via_rat_eqI, unfold if_distrib[of rat_of_int] of_int_diff of_int_mult
          d\<mu>[OF step(1) 1 i] dmu_ij_state[OF impl Linv state 1 i] step(5)[OF i jjm] id' c_def[symmetric]
          if_distrib[of "( * ) (rat_of_int (d fs (Suc jj)))"] ring_distribs,
          insert dmu_ij_state[OF impl Linv state _ jm], auto simp: gs.\<mu>.simps)
    qed
    {
      fix ii
      assume ii: "ii < m" "ii \<noteq> i" 
      hence "IArray.sub (IArray.of_fun (\<lambda>i. IArray.of_fun (d\<mu> fs i) (Suc i)) m) ii
        = IArray.of_fun (d\<mu> fs ii) (Suc ii)" by auto
      also have "\<dots> = IArray.of_fun (d\<mu> fs'' ii) (Suc ii)" 
      proof (rule iarray_of_fun_cong, goal_cases)
        case (1 j)
        with ii have j: "Suc j \<le> m" by auto
        show ?case unfolding d\<mu>_def by (subst step(6)[OF j], subst step(5), insert 1 ii, auto)
      qed
      finally have "IArray.sub (IArray.of_fun (\<lambda>i. IArray.of_fun (d\<mu> fs i) (Suc i)) m) ii 
         = IArray.of_fun (d\<mu> fs'' ii) (Suc ii)" by auto
    } note ii = this
    let ?mu'' = "iarray_update mu i (IArray.of_fun (d\<mu> fs'' i) i)" 
    have new_array: "?mu'' = IArray.of_fun (\<lambda> i. IArray.of_fun (d\<mu> fs'' i) i) m" 
      unfolding iarray_update_def iarray_length_of_fun to_mu_repr[OF impl Linv state, unfolded mu_repr_def]
      by (rule iarray_of_fun_cong, insert ii, auto)
    have d': "(map (?d fs) (rev [0..<j])) = (map (?d fs'') (rev [0..<j]))" 
      by (rule nth_equalityI, force, intro allI impI, simp, subst step(6), insert j i, auto
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
    have mu: "fs ! i - ?c \<cdot>\<^sub>v fs ! j = fs'' ! i" unfolding fs''[symmetric] using inv(7) i by auto
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
          by (rule iarray_of_fun_cong, subst step(6), auto)
      qed (auto simp: mu_repr_def)
    qed (insert i j, auto)
  qed
qed

lemma basis_reduction_add_rows: assumes
     impl: "LLL_impl_inv state i fs" 
  and inv: "LLL_invariant upw i fs" 
  and res: "basis_reduction_add_rows upw i state = state'" 
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
    have "basis_reduction_add_rows_loop state i i (small_fs_state state) = state'" by auto
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
  let ?n = "\<lambda> i. sq_norm (gso fs i)" 
  let ?n' = "\<lambda> i. sq_norm (gso fs'' i)" 
  let ?d = "d fs" 
  let ?d' = "d fs''" 
  let ?dn = "\<lambda> i. ?r (?d i * ?d i) * ?n i" 
  let ?dn' = "\<lambda> i. ?r (?d' i * ?d' i) * ?n' i" 
  let ?mu = "\<mu> fs" 
  let ?mu' = "\<mu> fs''" 
  let ?dmu = "\<lambda> i j. ?r (?d (Suc j)) * ?mu i j" 
  let ?dmu' = "\<lambda> i j. ?r (?d' (Suc j)) * ?mu' i j" 
  let ?dmus = "dmu_ij_state state" 
  let ?ds = "d_state state" 
  let ?idmu = "d\<mu> fs" 
  let ?idmu' = "d\<mu> fs''" 
  let ?x = "?n (i - 1)" 
  let ?y = "\<alpha> * ?n i" 
  let ?dd = "?n (i - 1) / ?n' (i - 1)" 
  let ?mui = "?mu i (i - 1)" 
  let ?mui' = "?mu' i (i - 1)" 
  note swap = basis_reduction_swap[OF inv i i0 cond refl, unfolded fs'']
  note dmu = d\<mu>[OF inv]
  note dmu' = d\<mu>[OF swap(1)]
  note inv' = LLL_invD[OF inv]
  have nim1: "?n i + square_rat (?mu i (i - 1)) * ?n (i - 1) = 
    ?n' (i - 1)" by (subst swap(4), insert i, auto)
  have ni: "?n i * (?n (i - 1) / ?n' (i - 1)) = ?n' i"
    by (subst swap(4)[of i], insert i i0, auto)
  have mu': "?mu i (i - 1) * (?n (i - 1) / ?n' (i - 1)) = ?mu' i (i - 1)"
    by (subst swap(5), insert i i0, auto)
  have fi: "fs ! (i - 1) = fs'' ! i" "fs ! i = fs'' ! (i - 1)" 
    unfolding fs''[symmetric] using inv'(7) i i0 by auto
  from res have upw': "upw' = False" "i' = i - 1" by auto
  let ?dmu_repr' = "swap_mu m mu i (?dmus i (i - 1)) (?d (i - 1)) (?d i) (?d (Suc i))" 
  let ?d'i = "(?d (Suc i) * ?d (i - 1) + ?dmus i (i - 1) * ?dmus i (i - 1)) div (?d i)" 
  from res[unfolded mu' nim1 ni, unfolded fi d_state_i] 
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
  have rat': "ii < m \<Longrightarrow> j < ii \<Longrightarrow> ?r (?idmu' ii j) = ?dmu' ii j" for ii j 
    using d\<mu>[OF swap(1), of j ii] 
     using LLL_mu_d_Z[OF swap(1), of j ii] by simp
  have rat: "ii < m \<Longrightarrow> j < ii \<Longrightarrow> ?dmu ii j = ?r (?dmus ii j)"
     "ii < m \<Longrightarrow> j < ii \<Longrightarrow> ?idmu ii j = ?dmus ii j" for ii j 
    using LLL_mu_d_Z[OF inv, of j ii]
    using dmu_ij_state[of j ii, symmetric] unfolding d\<mu>_def by auto
  from i0 have sim1: "Suc (i - 1) = i" by simp
  from LLL_d_Suc[OF inv im1, unfolded sim1] 
  have dn_im1: "?dn (i - 1) = ?r (?d i) * ?r (?d (i - 1))" by simp
  note pos = Gramian_determinant[OF inv le_refl] 
  from pos(2) have "?r (gs.Gramian_determinant fs m) \<noteq> 0" by auto
  from this[unfolded pos(1)] have nzero: "ii < m \<Longrightarrow> ?n ii \<noteq> 0" for ii by auto
  note pos = Gramian_determinant[OF swap(1) le_refl] 
  from pos(2) have "?r (gs.Gramian_determinant fs'' m) \<noteq> 0" by auto
  from this[unfolded pos(1)] have nzero': "ii < m \<Longrightarrow> ?n' ii \<noteq> 0" for ii by auto
  have dzero: "ii \<le> m \<Longrightarrow> ?d ii \<noteq> 0" for ii using LLL_d_pos[OF inv, of ii] by auto
  have dzero': "ii \<le> m \<Longrightarrow> ?d' ii \<noteq> 0" for ii using LLL_d_pos[OF swap(1), of ii] by auto

  {
    define start where "start = ?dmu' i (i - 1)" 
    have "start = (?n' (i - 1) / ?n (i - 1) * ?r (?d i)) * ?mu' i (i - 1)" 
      using start_def swap(6)[of i] i i0 by simp
    also have "?mu' i (i - 1) = ?mu i (i - 1) * (?n (i - 1) / ?n' (i - 1))" 
      using mu' by simp
    also have "(?n' (i - 1) / ?n (i - 1) * ?r (?d i)) * \<dots> = ?r (?d i) * ?mu i (i - 1)" 
      using nzero[OF im1] nzero'[OF im1] by simp
    also have "\<dots> = ?dmu i (i - 1)" using i0 by simp
    finally have "?dmu' i (i - 1) = ?dmu i (i - 1)" unfolding start_def .
  } note dmu_i_im1 = this
  have mu_ij: "ii < m \<Longrightarrow> j < ii \<Longrightarrow> ?dmus ii j = ?idmu ii j" for ii j
    using dmu_ij_state[symmetric, of j ii] dmu[of j ii] by auto
  note mu_ii = mu_ij[OF i \<open>i - 1 < i\<close>]
  { (* d updates *)
    fix j
    assume j: "j \<le> m" 
    define start where "start = ?d' j" 
    {
      assume jj: "j \<noteq> i" 
      have "?r start = ?r (?d' j)" unfolding start_def ..
      also have "?r (?d' j) = ?r (?d j)" 
        by (subst swap(6), insert j jj, auto)
      finally have "start = ?d j" by simp
    } note d_j = this 
    {
      assume jj: "j = i"  
      have "?r start = ?r (?d' i)" unfolding start_def unfolding jj by simp
      also have "\<dots> = ?n' (i - 1) / ?n (i - 1) * ?r (?d i)" 
        by (subst swap(6), insert i, auto)
      also have "?n' (i - 1) = (?r (?d i) / ?r (?d i)) * (?r (?d i) / ?r (?d i)) 
          * (?n i  + ?mu i (i - 1) * ?mu i (i - 1) * ?n (i - 1))" 
        by (subst swap(4)[OF im1], insert dzero[of i], insert i, simp)
      also have "?n (i - 1) = ?r (?d i) / ?r (?d (i - 1))" 
        unfolding LLL_d_Suc[OF inv im1, unfolded sim1] using dzero[of "i - 1"] i0 i by simp
      finally have "?r start = 
          ((?r (?d i) * ?n i) * ?r (?d (i - 1)) + ?dmu i (i - 1) * ?dmu i (i - 1)) 
          / (?r (?d i))" 
        using i0 dzero[of i] i dzero[of "i - 1"]
        by (simp add: ring_distribs)
      also have "?r (?d i) * ?n i = ?r (?d (Suc i))" 
        unfolding LLL_d_Suc[OF inv i] by simp
      also have "?dmu i (i - 1) = ?r (?dmus i (i - 1))" by (rule rat, insert i i0, auto)
      finally have "?r start = (?r (?d (Suc i) * ?d (i - 1) + ?dmus i (i - 1) * ?dmus i (i - 1)))
          / (?r (?d i))" by simp
      from division_to_div[OF this]
      have "start = ?d'i" .
    } note d_i = this
    from d_j d_i have "?d' j = (if j = i then ?d'i else ?d j)" unfolding start_def by auto
  } note d_update = this
  have "length fs'' = m" 
    using fs'' inv'(7) by auto
  hence fs_id: "fs' = fs''" unfolding fs' res fs_state.simps using of_list_repr[OF f_repr] 
    by (intro nth_equalityI, auto simp: o_def)
  from to_mu_repr[OF impl inv state] have mu: "mu_repr mu fs" by auto
  from to_d_repr[OF impl inv state] have d_repr: "d_repr ds fs" by auto
  note mu_def = mu[unfolded mu_repr_def]
  show ?g1 unfolding fs_id LLL_impl_inv.simps res
  proof (intro conjI f_repr)
    show "d_repr (iarray_update ds i ?d'i) fs''" 
      unfolding d_repr[unfolded d_repr_def] iarray_update_def d_repr_def iarray_length_of_fun
      by (rule iarray_of_fun_cong, subst d_update, auto simp: nth_append intro: arg_cong)
    show "mu_repr ?dmu_repr' fs''" unfolding mu_repr_def swap_mu_def Let_def mu_ii
    proof (rule iarray_of_fun_cong, goal_cases)
      case ii: (1 ii) 
      show ?case
      proof (cases "ii < i - 1")
        case small: True
        hence id: "(ii = i) = False" "(ii = i - 1) = False" "(i < ii) = False" "(ii < i - 1) = True" by auto
        have mu: "IArray.sub mu ii = IArray.of_fun (d\<mu> fs ii) ii" 
          using ii unfolding mu_def by auto
        show ?thesis unfolding id if_True if_False mu
        proof (rule iarray_of_fun_cong, goal_cases)
          case j: (1 j)
          with ii swap(5)[of ii j, unfolded id if_False] swap(6)[of "Suc j"] i i0 small show ?case 
            by (auto simp: d\<mu>_def)
        qed
      next
        case False
        hence iFalse: "(ii < i - 1) = False" by simp
        show ?thesis unfolding iFalse if_False if_distrib[of "\<lambda> f. IArray.of_fun f ii", symmetric]
          dmu_ij_state.simps[of f mu ds, folded state, symmetric] 
        proof (rule iarray_of_fun_cong, goal_cases)
          case j: (1 j)
          let ?start = "?idmu' ii j" 
          define start where "start = ?start" 
          from j ii have sj: "Suc j \<le> m" by auto
          note mu_ij[OF ii j]
          note rat'[OF ii j]
          note rat_ii_j = rat[OF ii j]
          note swaps = swap(5)[OF ii j] swap(6)[OF sj]
          from False consider (I) "ii = i" "j = i - 1" | (Is) "ii = i" "j \<noteq> i - 1" | 
            (Im1) "ii = i - 1" | (large) "ii > i" by linarith
          thus ?case
          proof cases
            case iii: Is
            with j have j: "j < i - 1" by auto
            have "?start = ?idmu (i - 1) j" unfolding swaps d\<mu>_def using iii ii i j i0 by auto
            also have "\<dots> = ?dmus (i - 1) j" by (subst mu_ij, insert iii i j , auto)
            finally show ?thesis using iii j by auto
          next
            case iii: I
            with j i0 have j: "j = i - 1" "Suc j = i" by auto
            have "?r (?start) = ?dmu' ii j" by fact
            also have "\<dots> = ?dmu i (i - 1)" unfolding iii j using dmu_i_im1 i0 by simp 
            also have "\<dots> = ?dmu ii j" unfolding j iii ..
            also have "\<dots> = ?r (?idmu ii j)" using rat_ii_j by simp
            finally have "?r ?start = ?r (?idmu ii j)" .
            hence "?start = ?idmu ii j" by simp
            thus ?thesis using iii by auto
          next
            case iii: Im1
            have "?start = ?idmu i j" unfolding swaps d\<mu>_def using iii ii i j i0 by auto
            also have "\<dots> = ?dmus i j" by (subst mu_ij, insert iii i j, auto)
            finally have id: "?start = ?dmus i j" .
            from iii have id': "(i < ii) = False" "(ii = i) = False" using i0 by auto
            show ?thesis unfolding id id' if_False ..
          next
            case iii: large
            hence id': "(i < ii) = True" by auto
            consider (jj) "j \<noteq> i - 1" "j \<noteq> i" | (ji) "j = i" | (jim1) "j = i - 1" by linarith
            thus ?thesis 
            proof cases
              case jj
              have "?start = ?idmu ii j" unfolding swaps d\<mu>_def using iii ii i jj i0 by auto
              also have "\<dots> = ?dmus ii j" by fact
              finally have id: "?start = ?dmus ii j" .
              show ?thesis unfolding id id' if_True using jj by auto
            next
              case ji
              have "?r start = ?dmu' ii j" unfolding start_def by fact
              also have "?r (?d' (Suc j)) = ?r (?d (Suc i))" unfolding swaps unfolding ji by simp 
              also have "?mu' ii j = ?mu ii (i - 1) - ?mu i (i - 1) * ?mu ii i" 
                unfolding swaps unfolding ji using i0 iii by auto
              also have "?r (?d (Suc i)) * \<dots> = ?r (?d (Suc i)) * ?r (?d i) / ?r (?d i) * \<dots>" 
                using dzero[of i] i by auto
              also have "\<dots> =  
                (?r (?d (Suc i)) * ?dmu ii (i - 1) - ?dmu i (i - 1) * ?dmu ii i) / ?r (?d i)" 
                using i0 by (simp add: field_simps)
              also have "\<dots> = 
                (?r (?d (Suc i)) * ?r (?dmus ii (i - 1)) - ?r (?dmus i (i - 1)) * ?r (?dmus ii i)) / ?r (?d i)" 
                by (subst (1 2 3) rat, insert i i0 ii iii, auto)
              also have "\<dots> = ?r (?d (Suc i) * ?dmus ii (i - 1) - ?dmus i (i - 1) * ?dmus ii i) / ?r (?d i)" 
                (is "_ = of_int ?x / _")
                by simp
              finally have "?r start = ?r ?x / ?r (?d i)" .
              from division_to_div[OF this]
              have id: "?start = (?d (Suc i) * ?dmus ii (i - 1) - ?dmus i (i - 1) * ?dmus ii i) div ?d i" 
                unfolding start_def .
              show ?thesis unfolding id' id if_True using mu_ii using ji by auto
            next
              case jim1
              hence id'': "(j = i - 1) = True" "(j = i) = False" using i0 by auto
              have "?r (start) = ?dmu' ii j" unfolding start_def by fact
              also have "?mu' ii j = ?mu ii (i - 1) * ?mu' i (i - 1) +
                                 ?mu ii i * ?n i / ?n' (i - 1)" (is "_ = ?x1 + ?x2")
                unfolding swaps unfolding jim1 using i0 iii by auto
              also have "?r (?d' (Suc j)) * (?x1 + ?x2)
                  = ?r (?d' (Suc j)) * ?x1 + ?r (?d' (Suc j)) * ?x2" by (simp add: ring_distribs)
              also have "?r (?d' (Suc j)) * ?x1 = ?dmu' i (i - 1) * (?r (?d i) * ?mu ii (i - 1))
                / ?r (?d i)"
                unfolding jim1 using i0 dzero[of i] i by simp
              also have "?dmu' i (i - 1) = ?dmu i (i - 1)" by fact
              also have "?r (?d i) * ?mu ii (i - 1) = ?dmu ii (i - 1)" using i0 by simp
              also have "?r (?d' (Suc j)) = ?n' (i - 1) * ?r (?d i) / ?n (i - 1)" 
                unfolding swaps unfolding jim1 using i0 i by simp 
              also have "\<dots> * ?x2 = (?n i * ?r (?d i)) / ?n (i - 1) * ?mu ii i" 
                using i0 nzero'[of "i - 1"] i by simp
              also have "?n i * ?r (?d i) = ?r (?d (Suc i))" unfolding LLL_d_Suc[OF inv i] ..
              also have "?r (?d (Suc i)) / ?n (i - 1) * ?mu ii i = ?dmu ii i / ?n (i - 1)" by simp
              also have "\<dots> = ?dmu ii i * ?r (?d (i - 1) * ?d (i - 1)) / ?dn (i - 1)" 
                using dzero[of "i - 1"] i by simp
              finally have "?r start = (?dmu i (i - 1) * ?dmu ii j * ?dn (i - 1) + 
                 ?dmu ii i * (?r (?d (i - 1) * ?d (i - 1) * ?d i))) / (?r (?d i) * ?dn (i - 1))"
                unfolding add_divide_distrib of_int_mult jim1
                using dzero[of "i - 1"] nzero[of "i - 1"] i dzero[of i] by auto
              also have "\<dots> = (?r (?dmus i (i - 1)) * ?r (?dmus ii j) * (?r (?d i) * ?r (?d (i - 1))) + 
                 ?r (?dmus ii i) * (?r (?d (i - 1) * ?d (i - 1) * ?d i))) / (?r (?d i) * (?r (?d i) * ?r (?d (i - 1))))" 
                unfolding dn_im1 
                by (subst (1 2 3) rat, insert i ii iii i0 j, auto)
              also have "\<dots> = (?r (?dmus i (i - 1)) * ?r (?dmus ii j) + ?r (?dmus ii i) * ?r (?d (i - 1))) 
                  / ?r (?d i)" 
                unfolding of_int_mult using dzero[of i] dzero[of "i - 1"] i i0 by (auto simp: field_simps)
              also have "\<dots> = ?r (?dmus i (i - 1) * ?dmus ii j + ?dmus ii i * ?d (i - 1)) / ?r (?d i)" 
                (is "_ = of_int ?x / _" )
                by simp
              finally have "?r start = ?r ?x / ?r (?d i)" .
              from division_to_div[OF this]
              have id: "?start = (?dmus i (i - 1) * ?dmus ii j + ?dmus ii i * ?d (i - 1)) div (?d i)" 
                unfolding start_def .
              show ?thesis unfolding id id' id'' if_True if_False mu_ii ..
            qed
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
  and res: "basis_reduction_step \<alpha> m upw i state = (upw',i',state')" 
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
    obtain state'' where state'': "basis_reduction_add_rows upw i state = state''" by auto
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
    note res = res[unfolded def id if_False Let_def state'' quot split d_state] 
    note pos = LLL_d_pos[OF inv le(1)] LLL_d_pos[OF inv le(2)] quotient_of_denom_pos[OF quot]
    from False have sim1: "Suc (i - 1) = i" by simp
    let ?r = "rat_of_int" 
    let ?x = "sq_norm (gso fs'' (i - 1))" 
    let ?y = "\<alpha> * sq_norm (gso fs'' i)" 
    have "(d fs'' i * d fs'' i * denom \<le> num * d fs'' (i - 1) * d fs'' (Suc i))
      = (?r (d fs'' i * d fs'' i * denom) \<le> ?r (num * d fs'' (i - 1) * d fs'' (Suc i)))" (is "?cond = _") by presburger
    also have "\<dots> = (?r (d fs'' i) * ?r (d fs'' i) * ?r denom \<le> ?r num * ?r (d fs'' (i - 1)) * ?r (d fs'' (Suc i)))" by simp
    also have "\<dots> = (?r (d fs'' i) * ?r (d fs'' i) \<le> \<alpha> * ?r (d fs'' (i - 1)) * ?r (d fs'' (Suc i)))" 
      using pos unfolding quotient_of_div[OF quot] by (auto simp: field_simps)
    also have "\<dots> = (?r (d fs'' i) / ?r (d fs'' (i - 1)) \<le> \<alpha> * (?r (d fs'' (Suc i)) / ?r (d fs'' i)))" 
      using pos by (auto simp: field_simps)
    also have "?r (d fs'' i) / ?r (d fs'' (i - 1)) = ?x" using LLL_d_Suc[OF inv, of "i - 1"] pos i False
      by (auto simp: field_simps)
    also have "\<alpha> * (?r (d fs'' (Suc i)) / ?r (d fs'' i)) = ?y" using LLL_d_Suc[OF inv i] pos i False
      by (auto simp: field_simps)
    finally have "?cond = (?x \<le> ?y)" .
    note res = res[unfolded this]
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
  and res: "basis_reduction_main \<alpha> m upw i state = state'" 
  and fs': "fs' = fs_state state'" 
shows "LLL_invariant True m fs'" 
      "LLL_impl_inv state' m fs'" 
proof (atomize(full), insert assms(1-3), induct "LLL_measure i fs" arbitrary: i fs upw state rule: less_induct)
  case (less i fs upw)
  have id: "LLL_invariant upw i fs = True" using less by auto
  note res = less(4)[unfolded basis_reduction_main.simps[of _ _ upw]]
  note inv = less(3)
  note impl = less(2)
  note IH = less(1)
  show ?case
  proof (cases "i < m")
    case i: True
    obtain i'' state'' upw'' where step: "basis_reduction_step \<alpha> m upw i state = (upw'',i'',state'')" 
      (is "?step = _") by (cases ?step, auto)
    with res i have res: "basis_reduction_main \<alpha> m upw'' i'' state'' = state'" by auto
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

lemma initial_state: "LLL_impl_inv (initial_state n m fs_init) 0 fs_init" 
proof -
  note conn = gs.main_connect[OF lin_dep, unfolded length_map, OF len refl]
  have id: "gram_schmidt n (RAT fs_init) = map (gso fs_init) [0..<m]" 
    using conn by auto
  have f_repr: "list_repr 0 ([], fs_init) (map ((!) fs_init) [0..<m])" 
    unfolding list_repr_def by (simp, intro nth_equalityI, auto simp: len)
  from fs_init have Rn: "set (RAT fs_init) \<subseteq> Rn" by auto
  have 1: "1 = d fs_init 0" unfolding d_def gs.Gramian_determinant_def gs.Gramian_matrix_def Let_def
    by (simp add: times_mat_def)
  define j where "j = m" 
  have jm: "j \<le> m" unfolding j_def by auto
  have 0: "0 = m - j" unfolding j_def by auto
  have d_repr: "d_repr (IArray (norms_to_ds 1 (map (\<lambda>j. \<parallel>gs.gso (map of_int_hom.vec_hom fs_init) j\<parallel>\<^sup>2) [0..<m]))) fs_init" 
    unfolding d_repr_def IArray.of_fun_def 1 0
  proof (rule arg_cong[of _ _ IArray], insert jm, induct j)
    case (Suc j)
    hence small: "m - Suc j < m" and [simp]: "Suc (m - Suc j) = m - j" by auto
    have id0: "snd (gs.main (RAT fs_init)) ! (m - Suc j) = gso fs_init (m - Suc j)" 
      unfolding conn using Suc by simp 
    from Suc(2-) have id1: "[m - Suc j..<m] = (m - Suc j) # [m - j ..<m]"
      "[m - Suc j..<Suc m] = (m - Suc j) # [m - j ..< Suc m]"
      by (auto simp add: Suc_diff_Suc Suc_le_lessD upt_conv_Cons)
    {
      fix j
      assume j: "j \<le> m" 
      have "gs.Gramian_determinant (RAT fs_init) j = of_int (d fs_init j)" 
        unfolding d_def
        by (rule of_int_Gramian_determinant, insert len fs_init j, auto simp: set_conv_nth)
    } note conv = this
    from Suc have le: "m - (Suc j) \<le> m" by auto
    note nzero = 
      gs.Gramian_determinant(2)[OF lin_dep, unfolded length_map, OF len refl le, unfolded conv[OF le]]
    have id': "(int_of_rat (rat_of_int (d fs_init (m - Suc j)) * \<parallel>gso fs_init (m - Suc j)\<parallel>\<^sup>2))
        = d fs_init (m - j)" 
      by (rule int_via_rat_eqI, 
      unfold gs.Gramian_determinant_div[OF lin_dep, unfolded length_map, OF len refl small, symmetric, unfolded id0],
      subst (1 2) conv, insert Suc(2-) nzero, auto)      
    show ?case unfolding id1 list.simps norms_to_ds.simps int_times_rat_def id'
      by (intro conjI[OF refl Suc(1)], insert Suc(2-), auto)
  qed simp
  show ?thesis unfolding initial_state_def Let_def LLL_impl_inv.simps gram_schmidt_triv id
    norms_mus_rat_norms_mus 
    gs.norms_mus[OF Rn, unfolded length_map len, OF gs.mn[OF lin_dep, unfolded length_map, OF len refl]]
    fst_conv snd_conv split
    by (intro conjI f_repr d_repr, unfold d_repr[unfolded d_repr_def] int_times_rat_def mu_repr_def d\<mu>_def,
      intro iarray_of_fun_cong, auto simp: nth_append)
qed

lemma basis_reduction: assumes res: "basis_reduction \<alpha> n fs_init = state" 
  and fs: "fs = fs_state state" 
shows "LLL_invariant True m fs" 
  "LLL_impl_inv state m fs" 
  using basis_reduction_main[OF initial_state LLL_inv_initial_state res[unfolded basis_reduction_def len] fs]
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