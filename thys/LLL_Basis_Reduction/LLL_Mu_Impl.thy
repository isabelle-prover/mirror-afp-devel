(*
    Authors:    Max Haslbeck
                René Thiemann
    License:    BSD
*)
subsection \<open>LLL Implementation which Stores the $\mu$-values and the Norms of the GSO\<close>

theory LLL_Mu_Impl
  imports LLL
   List_Representation
begin

text \<open>We store the $f$, $\mu$, and $||g||^2$ values.\<close>

definition iarray_update :: "'a iarray \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a iarray" where
  "iarray_update a i x = IArray.of_fun (\<lambda> j. if j = i then x else IArray.sub a j) (IArray.length a)" 

lemma iarray_of_fun_cong: "(\<And> i. i < n \<Longrightarrow> f i = g i) \<Longrightarrow> IArray.of_fun f n = IArray.of_fun g n" 
  unfolding IArray.of_fun_def by auto

lemma iarray_length_fun[simp]: "IArray.length (IArray.of_fun f n) = n" by simp

type_synonym LLL_gso_state = "int vec list_repr \<times> rat iarray iarray \<times> rat list_repr"

fun fi_state :: "LLL_gso_state \<Rightarrow> int vec" where
  "fi_state (f,mu,n) = get_nth_i f" 

fun fim1_state :: "LLL_gso_state \<Rightarrow> int vec" where
  "fim1_state (f,mu,n) = get_nth_im1 f" 

fun ni_state :: "LLL_gso_state \<Rightarrow> rat" where
  "ni_state (f,mu,n) = get_nth_i n" 

fun nim1_state :: "LLL_gso_state \<Rightarrow> rat" where
  "nim1_state (f,mu,n) = get_nth_im1 n" 

fun fs_state :: "LLL_gso_state \<Rightarrow> int vec list" where
  "fs_state (f,mu,n) = of_list_repr f" 

fun upd_fi_mu_state :: "LLL_gso_state \<Rightarrow> nat \<Rightarrow> int vec \<Rightarrow> rat iarray \<Rightarrow> LLL_gso_state" where
  "upd_fi_mu_state (f,mu,n) i fi mu_i = (update_i f fi, iarray_update mu i mu_i,n)" 

fun small_fs_state :: "LLL_gso_state \<Rightarrow> int vec list" where
  "small_fs_state (f,mu,n) = (fst f)" 

fun small_norms_state :: "LLL_gso_state \<Rightarrow> rat list" where
  "small_norms_state (f,mu,n) = (fst n)" 

fun mu_ij_state :: "LLL_gso_state \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> rat" where
  "mu_ij_state (f,mu,n) i j = (mu !! i !! j)" 

fun inc_state :: "LLL_gso_state \<Rightarrow> LLL_gso_state" where
  "inc_state (f,mu,n) = (inc_i f, mu, inc_i n)" 

fun basis_reduction_add_rows_loop where
  "basis_reduction_add_rows_loop state i j [] [] = state" 
| "basis_reduction_add_rows_loop state i sj (fj # fjs) (nj # njs) = (
     let fi = fi_state state;
         j = sj - 1;
         c = floor_ceil (mu_ij_state state i j);
         state' = (if c = 0 then state else upd_fi_mu_state state i (fi - c \<cdot>\<^sub>v fj) 
             (IArray.of_fun (\<lambda> jj. let mu = mu_ij_state state i jj in 
                  if jj < j then mu - of_int c * mu_ij_state state j jj else 
                  if jj = j then mu - of_int c else mu) i))
      in basis_reduction_add_rows_loop state' i j fjs njs)"
| "basis_reduction_add_rows_loop state _ _ _ _ = Code.abort (STR ''invalid invocation'') (\<lambda> _. state)" 

text \<open>More efficient code which breaks abstraction of state.\<close>

lemma basis_reduction_add_rows_loop_code: 
  "basis_reduction_add_rows_loop state i sj (fj # fjs) (nj # njs) = (
     case state of ((f1,f2),mus,norms) \<Rightarrow> 
     let fi = hd f2;
         j = sj - 1;
         mui = IArray.sub (IArray.sub mus i);
         c = floor_ceil (mui j)
      in (if c = 0 then 
          basis_reduction_add_rows_loop state i j fjs njs
         else  
             let muj = IArray.sub (IArray.sub mus j) in 
           basis_reduction_add_rows_loop
                ((f1,  (fi - c \<cdot>\<^sub>v fj) # tl f2), iarray_update mus i 
             (IArray.of_fun (\<lambda> jj. let mu = mui jj in 
                  if jj < j then mu - int_times_rat c (muj jj) else 
                  if jj = j then mu - of_int c else mu) i),
                norms) i j fjs njs))"
proof -
  obtain f1 f2 mus norms where state: "state = ((f1,f2),mus,norms)" by (cases state, auto)
  show ?thesis unfolding basis_reduction_add_rows_loop.simps Let_def 
      int_times_rat_def state split mu_ij_state.simps fi_state.simps get_nth_i_def update_i_def upd_fi_mu_state.simps
    by simp
qed

lemmas basis_reduction_add_rows_loop_code_equations =
  basis_reduction_add_rows_loop.simps(4,3,1) basis_reduction_add_rows_loop_code

declare basis_reduction_add_rows_loop_code_equations[code]

definition basis_reduction_add_rows where
  "basis_reduction_add_rows upw i state = 
     (if upw then basis_reduction_add_rows_loop state i i (small_fs_state state) (small_norms_state state) else state)" 

context
  fixes \<alpha> :: rat and n m :: nat and fs_init :: "int vec list" 
begin

definition swap_mu :: "rat iarray iarray \<Rightarrow> nat \<Rightarrow> rat \<Rightarrow> rat \<Rightarrow> rat \<Rightarrow> rat iarray iarray" where
  "swap_mu mu i mu_i_i mu_ii' ndiv = (let im1 = i - 1 in 
       IArray.of_fun (\<lambda> ii. if ii < im1 then IArray.sub mu ii else 
       if ii > i then let mu_ii = IArray.sub (IArray.sub mu ii) in 
           IArray.of_fun (\<lambda> j. let mu_ii_j = mu_ii j in 
               if j = i then mu_ii im1 - mu_i_i * mu_ii_j 
               else if j = im1 then mu_ii_j * mu_ii' + mu_ii i * ndiv 
               else mu_ii_j) ii else 
       if ii = i then let mu_im1 = IArray.sub (IArray.sub mu im1) in 
           IArray.of_fun (\<lambda> j. if j = im1 then mu_ii' else mu_im1 j) ii else 
           IArray.of_fun (IArray.sub (IArray.sub mu i)) ii) m)
            " 

definition basis_reduction_swap where
  "basis_reduction_swap i state = (let 
       ni = ni_state state;
       nim1 = nim1_state state;
       fi = fi_state state;
       fim1 = fim1_state state;
       mu = mu_ij_state state i (i - 1);
       fi' = fim1;
       fim1' = fi;
       nim1' = ni + square_rat mu * nim1;
       ndiv = nim1 / nim1';
       ni' = ni * ndiv;
       mu' = mu * ndiv
     in (case state of (f,mus,norms) \<Rightarrow>
         (False, i - 1, 
           (dec_i (update_im1 (update_i f fi') fim1'), 
            swap_mu mus i mu mu' (ni / nim1'), 
            dec_i (update_im1 (update_i norms ni') nim1')))))" 

text \<open>More efficient code which breaks abstraction of state.\<close>

lemma basis_reduction_swap_code[code]:
  "basis_reduction_swap i ((f1,f2), mus, (norms1, norms2)) = (let 
       ni = hd norms2;
       nim1 = hd norms1;
       fi = hd f2;
       fim1 = hd f1;
       im1 = i - 1;
       mu = IArray.sub (IArray.sub mus i) im1;
       fi' = fim1;
       fim1' = fi;
       nim1' = ni + square_rat mu * nim1;
       ndiv = nim1 / nim1';
       ni' = ni * ndiv;
       mu' = mu * ndiv
     in (False, im1, 
           ((tl f1,fim1' # fi' # tl f2), 
            swap_mu mus i mu mu' (ni / nim1'), 
            (tl norms1, nim1' # ni' # tl norms2))))" 
proof - 
  show ?thesis unfolding basis_reduction_swap_def split Let_def fi_state.simps fim1_state.simps 
    ni_state.simps nim1_state.simps get_nth_im1_def get_nth_i_def update_i_def update_im1_def dec_i_def
    by simp
qed

definition basis_reduction_step where
  "basis_reduction_step upw i state = (if i = 0 then (True, Suc i, inc_state state)
     else let 
       state' = basis_reduction_add_rows upw i state;
       ni = ni_state state';
       nim1 = nim1_state state'
    in if nim1 \<le> \<alpha> * ni then
          (True, Suc i, inc_state state') 
        else basis_reduction_swap i state')" 

partial_function (tailrec) basis_reduction_main where
  [code]: "basis_reduction_main upw i state = (if i < m
     then case basis_reduction_step upw i state of (upw',i',state') \<Rightarrow> 
       basis_reduction_main upw' i' state' else
       state)"

(* TODO: use better gram_schmidt, which already computes mu-values *)
definition "initial_state = (let
   gs = gram_schmidt_triv n (map (map_vec rat_of_int) fs_init)
  in (([], fs_init), 
  IArray.of_fun (\<lambda> i. let fi = of_int_hom.vec_hom (fs_init ! i) in 
  IArray.of_fun (\<lambda> j. if j = i then 1 else case gs ! j of (gj, nj) \<Rightarrow> fi \<bullet> gj / nj ) i) m, 
  ([],map snd gs)) :: LLL_gso_state)" 
end

definition "basis_reduction \<alpha> n fs = basis_reduction_main \<alpha> (length fs) True 0 (initial_state n (length fs) fs)" 

definition "reduce_basis \<alpha> fs = (case fs of Nil \<Rightarrow> fs | Cons f _ \<Rightarrow> fs_state (basis_reduction \<alpha> (dim_vec f) fs))" 

definition "short_vector \<alpha> fs = hd (reduce_basis \<alpha> fs)"

lemma map_rev_Suc: "map f (rev [0..<Suc j]) = f j # map f (rev [0..< j])" by simp

context LLL
begin

definition mu_repr :: "rat iarray iarray \<Rightarrow> int vec list \<Rightarrow> bool" where
  "mu_repr mu fs = (mu = IArray.of_fun (\<lambda> i. IArray.of_fun (\<lambda> j. \<mu> fs i j) i) m)" 

fun LLL_impl_inv :: "LLL_gso_state \<Rightarrow> nat \<Rightarrow> int vec list \<Rightarrow> bool" where
  "LLL_impl_inv (f,mu,norms) i fs = (list_repr i f (map (\<lambda> j. fs ! j) [0..<m])
    \<and> list_repr i norms (map (\<lambda> j. sq_norm (gso fs j)) [0..<m])
    \<and> mu_repr mu fs)" 

context fixes state i fs f mu norms
  assumes inv: "LLL_impl_inv state i fs"
  and state: "state = (f,mu,norms)" 
begin
lemma to_list_repr: "list_repr i f (map (\<lambda> j. fs ! j) [0..<m])"
  "list_repr i norms (map (\<lambda> j. sq_norm (gso fs j)) [0..<m])"
  using inv[unfolded state] by auto

lemma to_mu_repr: "mu_repr mu fs" using inv[unfolded state] by auto

lemma mu_ij_state: "j < ii \<Longrightarrow> ii < m \<Longrightarrow> mu_ij_state state ii j = \<mu> fs ii j" 
  unfolding to_mu_repr[unfolded mu_repr_def] state 
  by (auto simp: nth_append)

lemma fi_state: "i < m \<Longrightarrow> fi_state state = fs ! i"
  using get_nth_i[OF to_list_repr(1)] unfolding state by auto

lemma fim1_state: "i < m \<Longrightarrow> i \<noteq> 0 \<Longrightarrow> fim1_state state = fs ! (i - 1)"
  using get_nth_im1[OF to_list_repr(1)] unfolding state by auto

lemma ni_state: "i < m \<Longrightarrow> ni_state state = sq_norm (gso fs i)"
  using get_nth_i[OF to_list_repr(2)] unfolding state by auto

lemma nim1_state: "i < m \<Longrightarrow> i \<noteq> 0 \<Longrightarrow> nim1_state state = sq_norm (gso fs (i - 1))"
  using get_nth_im1[OF to_list_repr(2)] unfolding state by auto

lemma fs_state: "length fs = m \<Longrightarrow> fs_state state = fs"
  using of_list_repr[OF to_list_repr(1)] unfolding state by (auto simp: o_def intro!: nth_equalityI)

lemma LLL_state_inc_state: assumes Linv: "LLL_invariant upw i fs" 
  and i: "i < m" 
shows "LLL_impl_inv (inc_state state) (Suc i) fs" 
  "fs_state (inc_state state) = fs_state state" 
proof -
  from LLL_invD[OF Linv] have len: "length fs = m" by auto
  note inc = inc_i[OF to_list_repr(1)] inc_i[OF to_list_repr(2)] 
  from inc i inv show "LLL_impl_inv (inc_state state) (Suc i) fs" 
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
  and res: "basis_reduction_add_rows_loop state i j 
    (map (\<lambda> j. fs ! j) (rev [0 ..< j])) (map (\<lambda> j. sq_norm (gso fs j)) (rev [0 ..< j])) = state'" 
    (is "basis_reduction_add_rows_loop state i j (?mapf fs j) (?mapn fs j) = _")
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
  from fs_state[OF 0(1) _ len] have "fs_state state = fs" by (cases state, auto)
  thus ?case using 0 basis_reduction_add_row_done[of i fs] i fs' by auto
next
  case (Suc j fs state)
  hence j: "j < i" and id: "(j < i) = True" by auto
  obtain f mu norms where state: "state = (f,mu,norms)" by (cases state, auto)
  note Linv = Suc(3)
  note inv = LLL_invD[OF Linv]
  note impl = Suc(2)
  from fi_state[OF impl state i] have fi: "fi_state state = fs ! i" by auto
  have id: "Suc j - 1 = j" by simp
  note mu = mu_ij_state[OF impl state j i]
  note res = Suc(5)[unfolded map_rev_Suc basis_reduction_add_rows_loop.simps fi Let_def mu id int_times_rat_def]
  let ?c = "floor_ceil (\<mu> fs i j)" 
  show ?case
  proof (cases "?c = 0")
    case True
    from res[unfolded True] 
    have res: "basis_reduction_add_rows_loop state i j (?mapf fs j) (?mapn fs j) = state'" 
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
    have map_id_n: "?mapn fs j = ?mapn fs'' j"
      by (rule nth_equalityI, insert j step(4) i, auto simp: rev_nth fs''[symmetric])
    have nth_id: "[0..<m] ! i = i" using i by auto
    note res = res[unfolded False map_id_f map_id_n id if_False]
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
    let ?c' = "rat_of_int (floor_ceil (\<mu> fs i j))" 
    let ?mu' = "IArray.of_fun
       (\<lambda>jj. if jj < j then mu_ij_state state i jj - ?c' * mu_ij_state state j jj
             else if jj = j then mu_ij_state state i jj - ?c' else mu_ij_state state i jj) i" 
    have mu': "?mu' = IArray.of_fun (\<lambda> jj. \<mu> fs'' i jj) i" (is "_ = ?mu'i")
    proof (rule iarray_of_fun_cong, goal_cases)
      case (1 jj)
      with j i have jj: "jj \<le> i" and jm: "j < m" by auto
      show ?case unfolding mu_ij_state[OF impl state 1 i] using mu_ij_state[OF impl state _ jm]
        by (subst step(5)[OF i], insert 1 j i, auto simp: nth_append gs.\<mu>.simps)
    qed
    have repr_id:
      "map (\<lambda> i. fs ! i) [0..<m][i := (fs'' ! i)] = map (\<lambda> i. fs'' ! i) [0..<m]" (is "?xs = ?ys")
    proof (rule nth_equalityI, force, intro allI impI)
      fix j
      assume "j < length ?xs" 
      thus "?xs ! j = ?ys ! j" unfolding fs''[symmetric] i by (cases "j = i", auto)
    qed
    have repr_id': 
      "map (\<lambda> i. sq_norm (gso fs i)) [0..<m] = map (\<lambda> i. sq_norm (gso fs'' i)) [0..<m]"
      by (rule nth_equalityI, force, intro allI impI, insert step(4), auto)
    have mu: "fs ! i - ?c \<cdot>\<^sub>v fs ! j = fs'' ! i" unfolding fs''[symmetric] using inv(7) i by auto
    note res = res[unfolded mu' mu]
    show ?thesis unfolding step(3)[symmetric]
    proof (rule Suc(1)[OF _ step(1,2) res])
      note list_repr = to_list_repr[OF impl state]
      from i have ii: "i < length [0..<m]" by auto
      show "LLL_impl_inv (upd_fi_mu_state state i (fs'' ! i) ?mu'i) i fs''" 
        unfolding upd_fi_mu_state.simps state LLL_impl_inv.simps
      proof (intro conjI)
        show "list_repr i (update_i f (fs'' ! i)) (map ((!) fs'') [0..<m])" 
          using update_i[OF list_repr(1), unfolded length_map, OF ii] unfolding repr_id[symmetric] .
        show "list_repr i norms (map (\<lambda>j. \<parallel>gso fs'' j\<parallel>\<^sup>2) [0..<m])" using list_repr(2) unfolding repr_id' .
        {
          fix ii
          assume ii: "ii < m" "ii \<noteq> i" 
          hence "IArray.of_fun (\<lambda>i. IArray.of_fun (\<mu> fs i) (Suc i)) m !! ii
            = IArray.of_fun (\<mu> fs ii) (Suc ii)" by auto
          also have "\<dots> = IArray.of_fun (\<mu> fs'' ii) (Suc ii)" 
            by (rule iarray_of_fun_cong, subst step(5), insert ii, auto)
          finally have "IArray.of_fun (\<lambda>i. IArray.of_fun (\<mu> fs i) (Suc i)) m !! ii 
             = IArray.of_fun (\<mu> fs'' ii) (Suc ii)" by auto
        } note ii = this
        show "mu_repr (iarray_update mu i (IArray.of_fun (\<mu> fs'' i) i)) fs''" 
          unfolding to_mu_repr[OF impl state, unfolded mu_repr_def] iarray_update_def mu_repr_def 
           iarray_length_fun
          by (rule iarray_of_fun_cong, insert ii, auto)
      qed
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
  obtain f mu norms where state: "state = (f,mu,norms)" by (cases state, auto)
  note def = basis_reduction_add_rows_def
  show ?case
  proof (cases upw)
    case False
    from LLL_invD[OF inv] have len: "length fs = m" by auto
    from fs_state[OF impl state len] have "fs_state state = fs" by auto
    with assms False show ?thesis by (auto simp: def)
  next
    case True
    with inv have "LLL_invariant True i fs" by auto
    note start = this \<mu>_small_row_refl[of i fs]
    have id: "small_fs_state state = map (\<lambda> i. fs ! i) (rev [0..<i])"
       "small_norms_state state = map (\<lambda> i. sq_norm (gso fs i)) (rev [0..<i])"
      unfolding state using to_list_repr[OF impl state] i
      unfolding list_repr_def by (auto intro!: nth_equalityI simp: nth_rev min_def)
    from res[unfolded def] True 
    have "basis_reduction_add_rows_loop state i i (small_fs_state state) (small_norms_state state) = state'" by auto
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
  from i i0 have ii: "i - 1 < i" by auto
  obtain f mu norms where state: "state = (f,mu,norms)" by (cases state, auto)
  note mu_ij_state = mu_ij_state[OF impl state]
  note res = res[unfolded basis_reduction_swap_def Let_def split state, folded state, unfolded
    ni_state[OF impl state i] nim1_state[OF impl state i i0]
    fi_state[OF impl state i] fim1_state[OF impl state i i0] mu_ij_state[OF ii i]] 
  from LLL_invD[OF inv] have len: "length fs = m" by auto
  from fs_state[OF impl state len] have fs: "fs_state state = fs" by auto
  obtain fs'' where fs'': "fs[i := fs ! (i - 1), i - 1 := fs ! i] = fs''" by auto
  let ?n = "\<lambda> i. sq_norm (gso fs i)" 
  let ?n' = "\<lambda> i. sq_norm (gso fs'' i)" 
  let ?mu = "\<mu> fs" 
  let ?mu' = "\<mu> fs''" 
  let ?x = "?n (i - 1)" 
  let ?y = "\<alpha> * ?n i" 
  let ?d = "?n (i - 1) / ?n' (i - 1)" 
  let ?mui = "?mu i (i - 1)" 
  let ?mui' = "?mu' i (i - 1)" 
  note swap = basis_reduction_swap[OF inv i i0 cond refl, unfolded fs'']
  note inv' = LLL_invD[OF inv]
  have nim1: "?n i + square_rat (?mu i (i - 1)) * ?n (i - 1) = 
    ?n' (i - 1)" by (subst swap(4), insert i, auto)
  have ni: "?n i * (?n (i - 1) / ?n' (i - 1)) = ?n' i"
    by (subst swap(4)[of i], insert i i0, auto)
  have mu': "?mu i (i - 1) * (?n (i - 1) / ?n' (i - 1)) = ?mu' i (i - 1)"
    by (subst swap(5), insert i i0, auto)
  have fi: "fs ! (i - 1) = fs'' ! i" "fs ! i = fs'' ! (i - 1)" 
    unfolding fs''[symmetric] using inv'(7) i i0 by auto
  let ?mu_repr' = "swap_mu m mu i ?mui ?mui' (?n i / ?n' (i - 1))" 
  from res[unfolded mu' nim1 ni, unfolded fi] 
  have res: "upw' = False" "i' = i - 1" 
    "state' = (dec_i (update_im1 (update_i f (fs'' ! i)) (fs'' ! (i - 1))), 
       ?mu_repr',
       dec_i (update_im1 (update_i norms (?n' i)) (?n' (i - 1))))" by auto
  from i have ii: "i < length [0..<m]" and im1: "i - 1 < m" by auto
  note list_repr = to_list_repr[OF impl state]
  from dec_i[OF update_im1[OF update_i[OF list_repr(1)]], unfolded length_map, OF ii i0 i0]
  have 
    "list_repr (i - 1) (dec_i (update_im1 (update_i f (fs'' ! i)) (fs'' ! (i - 1)))) (map ((!) fs) [0..<m][i := (fs'' ! i), 
       i - 1 := (fs'' ! (i - 1))])" (is "list_repr _ ?fr ?xs") .
  also have "?xs = map ((!) fs'') [0..<m]" unfolding fs''[symmetric]
    by (intro nth_equalityI, insert i i0 len, auto simp: nth_append, rename_tac ii, case_tac "ii \<in> {i-1,i}", auto)
  finally have f_repr: "list_repr (i - 1) ?fr (map ((!) fs'') [0..<m])" .
  from dec_i[OF update_im1[OF update_i[OF list_repr(2)]], unfolded length_map, OF ii i0 i0]
  have 
    "list_repr (i - 1) (dec_i (update_im1 (update_i norms (?n' i)) (?n' (i - 1)))) (map ?n [0..<m][i := ?n' i, 
       i - 1 := ?n' (i - 1)])" (is "list_repr _ ?nr ?xs") .
  also have "?xs = map ?n' [0..<m]" 
    by (intro nth_equalityI, insert i i0 len, auto simp: nth_append, rename_tac ii, case_tac "ii \<in> {i-1,i}", auto simp: swap(4))
  finally have n_repr: "list_repr (i - 1) ?nr (map ?n' [0..<m])" .
  have "length fs'' = m" 
    using fs'' inv'(7) by auto
  hence fs_id: "fs' = fs''" unfolding fs' res fs_state.simps using of_list_repr[OF f_repr] 
    by (intro nth_equalityI, auto simp: o_def)
  from to_mu_repr[OF impl state] have mu: "mu_repr mu fs" by auto
  note mu_def = mu[unfolded mu_repr_def]
  show ?g1 unfolding fs_id LLL_impl_inv.simps res
  proof (intro conjI n_repr f_repr)
    show "mu_repr ?mu_repr' fs''" unfolding mu_repr_def swap_mu_def Let_def
    proof (rule iarray_of_fun_cong, goal_cases)
      case (1 ii) 
      consider (small) "ii < i - 1" | (I) "ii = i" | (Im1) "ii = i - 1" | (large) "ii > i" by linarith
      thus ?case
      proof (cases)
        case small
        hence id: "(ii = i) = False" "(ii = i - 1) = False" "(i < ii) = False" "(ii < i - 1) = True" by auto
        have mu': "IArray.of_fun (?mu' ii) ii = IArray.of_fun (?mu ii) ii" 
        proof (rule iarray_of_fun_cong, goal_cases)
          case j: (1 j)
          with 1 swap(5)[of ii j, unfolded id if_False] i i0 small show ?case by auto
        qed
        show ?thesis unfolding id if_True mu' unfolding mu_def using small i by auto
      next
        case I
        hence id: "(ii = i) = True"  "(ii < i - 1) = False" "(i < ii) = False" by auto
        show ?thesis unfolding id if_True if_False Let_def unfolding I
        proof (rule iarray_of_fun_cong, goal_cases)
          case j: (1 j)
          show ?case
          proof (cases "j < i")
            case True
            from swap(5)[OF i True] i True show ?thesis by (auto simp: mu_def)
          qed (insert j, auto simp: gs.\<mu>.simps)
        qed
      next
        case Im1
        hence id: "(ii = i) = False"  "(i < ii) = False" "(ii < i - 1) = False" 
          "(ii = i - 1) = True" "(Suc ii) = i" using i0 by auto
        show ?thesis unfolding id if_False if_True Let_def unfolding Im1
        proof (rule iarray_of_fun_cong, goal_cases)
          case j: (1 j)
          show ?case
          proof (cases "j < i - 1")
            case True
            from swap(5)[OF im1 True] im1 i True i0 id show ?thesis by (auto simp: mu_def)
          qed (insert j Im1, auto simp: gs.\<mu>.simps)
        qed
      next
        case large
        hence id: "(ii = i) = False"  "(ii < i - 1) = False" "(i < ii) = True" "(ii = i - 1) = False" using i0 by auto
        show ?thesis unfolding id if_False if_True Let_def 
        proof (rule iarray_of_fun_cong, goal_cases)
          case j: (1 j)
          show ?case
          proof (cases "j < ii")
            case True
            have id': "(True \<and> b) = b" for b by auto
            have mu: "k < ii \<Longrightarrow> mu !! ii !! k = \<mu> fs ii k" for k 
              unfolding mu_def using 1 by (auto simp: nth_append)
            from large have i1: "i - 1 < ii" by auto
            show ?thesis unfolding swap(5)[OF 1 True] 
              unfolding id if_False mu[OF i1] mu[OF True] mu[OF large] id'
              by (rule if_cong[OF refl _ if_cong[OF refl _ refl]], auto)
          qed (insert j large 1, auto simp: mu_def gs.\<mu>.simps)
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
  obtain f mu norms where state: "state = (f,mu,norms)" by (cases state, auto)
  note def = basis_reduction_step_def
  from LLL_invD[OF inv] have len: "length fs = m" by auto
  from fs_state[OF impl state len] have fs: "fs_state state = fs" by auto
  show ?case
  proof (cases "i = 0")
    case True
    from LLL_state_inc_state[OF impl state inv i] i
      assms increase_i[OF inv i True] True 
      res fs' fs
    show ?thesis by (auto simp: def)
  next
    case False
    hence id: "(i = 0) = False" by auto
    obtain state'' where state'': "basis_reduction_add_rows upw i state = state''" by auto
    define fs'' where fs'': "fs'' = fs_state state''" 
    obtain f mu norms where state: "state'' = (f,mu,norms)" by (cases state'', auto)
    from basis_reduction_add_rows[OF impl inv state'' i fs'']
    have inv: "LLL_invariant False i fs''"
      and meas: "LLL_measure i fs = LLL_measure i fs''" 
      and impl: "LLL_impl_inv state'' i fs''" by auto
    note res = res[unfolded def id if_False Let_def state'' 
        nim1_state[OF impl state i False] ni_state[OF impl state i]] 
    let ?x = "sq_norm (gso fs'' (i - 1))" 
    let ?y = "\<alpha> * sq_norm (gso fs'' i)" 
    show ?thesis
    proof (cases "?x \<le> ?y")
      case True
      from increase_i[OF inv i _ True] True res meas LLL_state_inc_state[OF impl state inv i] fs' fs''
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
    obtain f mu norms where state: "state = (f,mu,norms)" by (cases state, auto)
    from fs_state[OF impl state len] have fs: "fs_state state = fs" by auto
    from False LLL_invD[OF inv] have i: "i = m" upw by auto
    with False res inv impl fs show ?thesis by (auto simp: fs')
  qed
qed

lemma initial_state: "LLL_impl_inv (initial_state n m fs_init) 0 fs_init" 
proof -
  have id: "gram_schmidt n (RAT fs_init) = map (gso fs_init) [0..<m]" 
    using gs.main_connect[OF lin_dep, unfolded length_map, OF len refl] by auto
  have f_repr: "list_repr 0 ([], fs_init) (map ((!) fs_init) [0..<m])" 
    unfolding list_repr_def by (simp, intro nth_equalityI, auto simp: len)
  have n_repr: "list_repr 0
     ([], map snd (map (\<lambda>x. (x, \<parallel>x\<parallel>\<^sup>2)) (map (gso fs_init) [0..<m])))
     (map (\<lambda>j. \<parallel>gso fs_init j\<parallel>\<^sup>2) [0..<m])" 
    unfolding list_repr_def by simp
  show ?thesis unfolding initial_state_def Let_def LLL_impl_inv.simps gram_schmidt_triv id
    by (intro conjI f_repr n_repr, auto simp: mu_repr_def gs.\<mu>.simps len)
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