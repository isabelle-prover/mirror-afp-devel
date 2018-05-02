(*
    Authors:    Jose Divasón
                Maximilian Haslbeck
                Sebastiaan Joosten
                René Thiemann
                Akihisa Yamada
    License:    BSD
*)
subsection \<open>LLL Implementation which Stores the GSO and their Norms\<close>

theory LLL_GSO_Impl
  imports LLL
   List_Representation
begin

text \<open>We store the $f$, $g$, and $||g||^2$ values.\<close>

type_synonym LLL_gso_state = "(int vec \<times> rat vec \<times> rat) list_repr"

definition scalar_prod_int_rat :: "int vec \<Rightarrow> rat vec \<Rightarrow> rat" (infix "\<bullet>i" 70) where
  "x \<bullet>i y = (y \<bullet> map_vec rat_of_int x)"

definition fi_state :: "LLL_gso_state \<Rightarrow> int vec" where
  "fi_state state = fst (get_nth_i state)" 

definition fim1_state :: "LLL_gso_state \<Rightarrow> int vec" where
  "fim1_state state = fst (get_nth_im1 state)" 

definition ni_state :: "LLL_gso_state \<Rightarrow> rat" where
  "ni_state state = snd (snd (get_nth_i state))" 

definition nim1_state :: "LLL_gso_state \<Rightarrow> rat" where
  "nim1_state state = snd (snd (get_nth_im1 state))" 

definition gi_state :: "LLL_gso_state \<Rightarrow> rat vec" where
  "gi_state state = fst (snd (get_nth_i state))" 

definition gim1_state :: "LLL_gso_state \<Rightarrow> rat vec" where
  "gim1_state state = fst (snd (get_nth_im1 state))" 

definition fs_state :: "LLL_gso_state \<Rightarrow> int vec list" where
  "fs_state state = map fst (of_list_repr state)" 

definition upd_fi_state :: "LLL_gso_state \<Rightarrow> int vec \<Rightarrow> LLL_gso_state" where
  "upd_fi_state state fi = (case get_nth_i state of (_,gi,ngi) \<Rightarrow> update_i state (fi,gi,ngi))" 

definition small_fs_gso_norms :: "LLL_gso_state \<Rightarrow> (int vec \<times> rat vec \<times> rat)list" where
  "small_fs_gso_norms = fst" 

fun basis_reduction_add_rows_loop where
  "basis_reduction_add_rows_loop state [] = state" 
| "basis_reduction_add_rows_loop state ((fj,gj,ngj) # rest) = (
     let fi = fi_state state;
         c = floor_ceil ((fi \<bullet>i gj) / ngj);
         state' = (if c = 0 then state else upd_fi_state state (fi - c \<cdot>\<^sub>v fj))
      in basis_reduction_add_rows_loop state' rest)" 

definition basis_reduction_add_rows where
  "basis_reduction_add_rows upw state = 
     (if upw then basis_reduction_add_rows_loop state (small_fs_gso_norms state) else state)" 

context
  fixes \<alpha> :: rat and n m :: nat and fs_init :: "int vec list" 
begin

definition basis_reduction_swap where
  "basis_reduction_swap i state = (let 
       ni = ni_state state;
       nim1 = nim1_state state;
       fi = fi_state state;
       fim1 = fim1_state state;
       gi = gi_state state;
       gim1 = gim1_state state;
       mu = (fi \<bullet>i gim1) / nim1;
       fi' = fim1;
       fim1' = fi;
       gim1' = gi + mu \<cdot>\<^sub>v gim1;
       nim1' = ni + square_rat mu * nim1;
       gi' = gim1 - ((fim1 \<bullet>i gim1') / nim1') \<cdot>\<^sub>v gim1';
       ni' = ni * nim1 / nim1'
     in (False, i - 1, dec_i (update_im1 (update_i state (fi',gi',ni')) (fim1',gim1',nim1'))))" 

definition basis_reduction_step where
  "basis_reduction_step upw i state = (if i = 0 then (True, Suc i, inc_i state)
     else let 
       state' = basis_reduction_add_rows upw state;
       ni = ni_state state';
       nim1 = nim1_state state'
    in if nim1 \<le> \<alpha> * ni then
          (True, Suc i, inc_i state') 
        else basis_reduction_swap i state')" 

partial_function (tailrec) basis_reduction_main where
  [code]: "basis_reduction_main upw i state = (if i < m
     then case basis_reduction_step upw i state of (upw',i',state') \<Rightarrow> 
       basis_reduction_main upw' i' state' else
       state)"

definition "initial_state = (let
   gs = gram_schmidt_triv n (map (map_vec rat_of_int) fs_init)
  in ([],(zip fs_init gs)) :: LLL_gso_state)" 
end

definition "basis_reduction \<alpha> n fs = basis_reduction_main \<alpha> (length fs) True 0 (initial_state n fs)" 

definition "reduce_basis \<alpha> fs = (case fs of Nil \<Rightarrow> fs | Cons f _ \<Rightarrow> fs_state (basis_reduction \<alpha> (dim_vec f) fs))" 

definition "short_vector \<alpha> fs = hd (reduce_basis \<alpha> fs)"

lemma map_rev_Suc: "map f (rev [0..<Suc j]) = f j # map f (rev [0..< j])" by simp

context LLL
begin

abbreviation fgn where "fgn fs j \<equiv> (fs ! j, gso fs j, sq_norm (gso fs j))" 

definition LLL_impl_inv :: "LLL_gso_state \<Rightarrow> nat \<Rightarrow> int vec list \<Rightarrow> bool" where
  "LLL_impl_inv state i fs = list_repr i state (map (fgn fs) [0..<m])" 

context fixes state i fs
  assumes inv: "LLL_impl_inv state i fs"
begin
lemma to_list_repr: "list_repr i state (map (fgn fs) [0..<m])" 
  using inv unfolding LLL_impl_inv_def by auto

lemma fi_state: "i < m \<Longrightarrow> fi_state state = fs ! i"
  using get_nth_i[OF to_list_repr] unfolding fi_state_def by auto

lemma fim1_state: "i < m \<Longrightarrow> i \<noteq> 0 \<Longrightarrow> fim1_state state = fs ! (i - 1)"
  using get_nth_im1[OF to_list_repr] unfolding fim1_state_def by auto

lemma gi_state: "i < m \<Longrightarrow> gi_state state = gso fs i"
  using get_nth_i[OF to_list_repr] unfolding gi_state_def by auto

lemma gim1_state: "i < m \<Longrightarrow> i \<noteq> 0 \<Longrightarrow> gim1_state state = gso fs (i - 1)"
  using get_nth_im1[OF to_list_repr] unfolding gim1_state_def by auto

lemma ni_state: "i < m \<Longrightarrow> ni_state state = sq_norm (gso fs i)"
  using get_nth_i[OF to_list_repr] unfolding ni_state_def by auto

lemma nim1_state: "i < m \<Longrightarrow> i \<noteq> 0 \<Longrightarrow> nim1_state state = sq_norm (gso fs (i - 1))"
  using get_nth_im1[OF to_list_repr] unfolding nim1_state_def by auto

lemma fs_state: "length fs = m \<Longrightarrow> fs_state state = fs"
  using of_list_repr[OF to_list_repr] unfolding fs_state_def by (auto simp: o_def intro!: nth_equalityI)

lemma LLL_state_inc_i: assumes inv: "LLL_invariant upw i fs" 
  and i: "i < m" 
shows "LLL_impl_inv (inc_i state) (Suc i) fs" 
  "fs_state (inc_i state) = fs_state state" 
proof -
  from LLL_invD[OF inv] have len: "length fs = m" by auto
  note inc =  inc_i[OF to_list_repr] 
  from inc i show "LLL_impl_inv (inc_i state) (Suc i) fs" 
    unfolding LLL_impl_inv_def by auto
  from of_list_repr[OF inc] of_list_repr[OF to_list_repr] i
  show "fs_state (inc_i state) = fs_state state" unfolding fs_state_def by auto
qed
end
end

context LLL_with_assms
begin
lemma basis_reduction_add_rows_loop: assumes
    impl: "LLL_impl_inv state i fs" 
  and inv: "LLL_invariant True i fs" 
  and mu_small: "\<mu>_small_row i fs j"
  and res: "basis_reduction_add_rows_loop state (map (fgn fs) (rev [0 ..< j])) = state'" 
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
  from fs_state[OF 0(1) len] have "fs_state state = fs" by auto
  thus ?case using 0 basis_reduction_add_row_done[of i fs] i fs' by auto
next
  case (Suc j fs state)
  hence j: "j < i" and id: "(j < i) = True" by auto
  note Linv = Suc(3)
  note inv = LLL_invD[OF Linv]
  note impl = Suc(2)
  from fi_state[OF impl i] have fi: "fi_state state = fs ! i" by auto
  have mu: "fs ! i \<bullet>i gso fs j / \<parallel>gso fs j\<parallel>\<^sup>2 = \<mu> fs i j" 
    unfolding scalar_prod_int_rat_def gs.\<mu>.simps id if_True
    by (subst comm_scalar_prod, insert j i inv, auto)
  note res = Suc(5)[unfolded map_rev_Suc basis_reduction_add_rows_loop.simps fi Let_def mu]
  let ?c = "floor_ceil (\<mu> fs i j)" 
  show ?case
  proof (cases "?c = 0")
    case True
    from res[unfolded True] 
    have res: "basis_reduction_add_rows_loop state (map (fgn fs) (rev [0..<j])) = state'" 
      by simp
    note step = Linv basis_reduction_add_row_main_0[OF Linv i j True Suc(4)]
    show ?thesis using Suc(1)[OF impl step(1-2) res _ i] j by auto
  next
    case False
    hence id: "(?c = 0) = False" by auto
    from i have ii: "i < length (map (fgn fs) [0..<m])" and iii: "i < length [0..<m]" by auto
    define fi' where "fi' = fs ! i - ?c \<cdot>\<^sub>v fs ! j" 
    obtain fs'' where fs'': "fs[i := fs ! i - ?c \<cdot>\<^sub>v fs ! j] = fs''" by auto
    note step = basis_reduction_add_row_main[OF Linv i j refl refl Suc(4), unfolded fs'']
    have map_id: "map (fgn fs) (rev [0..<j]) = map (fgn fs'') (rev [0..<j])" 
      by (rule nth_equalityI, insert j step(4) i, auto simp: rev_nth fs''[symmetric])
    have nth_id: "[0..<m] ! i = i" using i by auto
    note res = res[unfolded False map_id id if_False]
    have fi: "fi' = fs'' ! i" unfolding fs''[symmetric] fi'_def using inv(7) i by auto
    have repr_id: "(map (fgn fs) [0..<m] [i := (fs'' ! i, gso fs'' i, \<parallel>gso fs'' i\<parallel>\<^sup>2)])
      = (map (fgn fs'') [0..<m])" (is "?xs = ?ys") 
    proof (rule nth_equalityI, force, intro allI impI)
      fix j
      assume "j < length ?xs" 
      thus "?xs ! j = ?ys ! j" 
        using step(4) unfolding fs''[symmetric] i 
        by (cases "j = i", auto)
    qed
    show ?thesis unfolding step(3)[symmetric] 
    proof (rule Suc(1)[OF _ step(1,2) res])
      note list_repr = to_list_repr[OF impl]
      show "LLL_impl_inv (upd_fi_state state (fs ! i - ?c \<cdot>\<^sub>v fs ! j)) i fs''" 
        unfolding fi'_def[symmetric] upd_fi_state_def 
        using update_i[OF list_repr ii, of "(fi', gso fs i, sq_norm (gso fs i))"] i
        unfolding get_nth_i[OF list_repr ii] nth_map[OF iii] split LLL_impl_inv_def
          step(4)[OF i, symmetric] nth_id 
        unfolding fi repr_id by auto
    qed (insert i j, auto)
  qed
qed

lemma basis_reduction_add_rows: assumes
     impl: "LLL_impl_inv state i fs" 
  and inv: "LLL_invariant upw i fs" 
  and res: "basis_reduction_add_rows upw state = state'" 
  and i: "i < m" 
  and fs': "fs' = fs_state state'" 
shows 
  "LLL_impl_inv state' i fs'" 
  "LLL_invariant False i fs'" 
  "LLL_measure i fs' = LLL_measure i fs" 
proof (atomize(full), goal_cases)
  case 1
  note def = basis_reduction_add_rows_def
  show ?case
  proof (cases upw)
    case False
    from LLL_invD[OF inv] have len: "length fs = m" by auto
    from fs_state[OF impl len] have "fs_state state = fs" by auto
    with assms False show ?thesis by (auto simp: def)
  next
    case True
    with inv have "LLL_invariant True i fs" by auto
    note start = this \<mu>_small_row_refl[of i fs]
    have id: "small_fs_gso_norms state = map (fgn fs) (rev [0..<i])" 
      unfolding small_fs_gso_norms_def using to_list_repr[OF impl] i
      unfolding list_repr_def by (auto intro!: nth_equalityI simp: nth_rev min_def)
    from res[unfolded def] True 
    have "basis_reduction_add_rows_loop state (small_fs_gso_norms state) = state'" by auto
    from basis_reduction_add_rows_loop[OF impl start(1-2) this[unfolded id] le_refl i fs']
    show ?thesis by auto
  qed
qed

lemma basis_reduction_swap: assumes 
  impl: "LLL_impl_inv state i fs" 
  and inv: "LLL_invariant False i fs" 
  and res: "basis_reduction_swap i state = (upw',i',state')" 
  and cond: "sq_norm (gso fs (i - 1)) > \<alpha> * sq_norm (gso fs i)" 
  and i: "i < m" and i0: "i \<noteq> 0" 
  and fs': "fs' = fs_state state'" 
shows 
  "LLL_impl_inv state' i' fs'" (is ?g1)
  "LLL_invariant upw' i' fs'" (is ?g2)
  "LLL_measure i' fs' < LLL_measure i fs" (is ?g3)
proof -
  note res = res[unfolded basis_reduction_swap_def Let_def 
    ni_state[OF impl i] nim1_state[OF impl i i0]
    fi_state[OF impl i] fim1_state[OF impl i i0] 
    gi_state[OF impl i] gim1_state[OF impl i i0]]
  from LLL_invD[OF inv] have len: "length fs = m" by auto
  from fs_state[OF impl len] have fs: "fs_state state = fs" by auto
  let ?x = "sq_norm (gso fs (i - 1))" 
  let ?y = "\<alpha> * sq_norm (gso fs i)" 
  obtain fs'' where fs'': "fs[i := fs ! (i - 1), i - 1 := fs ! i] = fs''" by auto
  note swap = basis_reduction_swap[OF inv i i0 cond refl, unfolded fs'']
  note inv' = LLL_invD[OF inv]
  have mu: "fs ! i \<bullet>i gso fs (i - 1) / \<parallel>gso fs (i - 1)\<parallel>\<^sup>2 = \<mu> fs i (i - 1)" 
    unfolding gs.\<mu>.simps scalar_prod_int_rat_def
    by (subst comm_scalar_prod, insert i0 i inv', auto)
  have nim1: "\<parallel>gso fs i\<parallel>\<^sup>2 + square_rat (\<mu> fs i (i - 1)) * \<parallel>gso fs (i - 1)\<parallel>\<^sup>2 = 
    sq_norm (gso fs'' (i - 1))" by (subst swap(4), insert i, auto)
  have ni: "\<parallel>gso fs i\<parallel>\<^sup>2 * \<parallel>gso fs (i - 1)\<parallel>\<^sup>2 / \<parallel>gso fs'' (i - 1)\<parallel>\<^sup>2 = \<parallel>gso fs'' i\<parallel>\<^sup>2"
    by (subst swap(4)[of i], insert i i0, auto)
  have gim1: "gso fs i + \<mu> fs i (i - 1) \<cdot>\<^sub>v gso fs (i - 1) = gso fs'' (i - 1)" 
    by (subst swap(3), insert i i0, auto)
  have id': "fs ! (i - 1) \<bullet>i gso fs'' (i - 1) = 
    (RAT fs ! (i - 1) \<bullet> gso fs'' (i - 1))" 
    unfolding scalar_prod_int_rat_def
    by (subst comm_scalar_prod, insert i0 i inv'(2-6) LLL_invD(2-6)[OF swap(1)], auto)
  have gi: "gso fs (i - 1) - fs ! (i - 1) \<bullet>i gso fs'' (i - 1) / \<parallel>gso fs'' (i - 1)\<parallel>\<^sup>2 \<cdot>\<^sub>v
     gso fs'' (i - 1) = gso fs'' i"     
    by (subst swap(3)[of i, OF i], unfold id', insert i i0, auto)
  have fi: "fs ! (i - 1) = fs'' ! i" "fs ! i = fs'' ! (i - 1)" 
    unfolding fs''[symmetric] using inv'(7) i i0 by auto
  from res[unfolded mu nim1 ni, unfolded gim1 gi, unfolded fi] 
  have res: "upw' = False" "i' = i - 1" 
    "state' = dec_i (update_im1
     (update_i state (fgn fs'' i)) (fgn fs'' (i - 1)))" by auto
  from i have ii: "i < length [0..<m]" by auto
  from dec_i[OF update_im1[OF update_i[OF to_list_repr[OF impl], 
      unfolded length_map, OF ii, of "fgn fs'' i"] i0, of "fgn fs'' (i - 1)"] i0,
    folded res(3)]
  have repr: "list_repr (i - 1) state'
    ((map (fgn fs) [0..< m]) [ i := fgn fs'' i, i - 1 := fgn fs'' (i - 1)])" by simp
  also have "((map (fgn fs) [0..< m]) [ i := fgn fs'' i, i - 1 := fgn fs'' (i - 1)])
    = map (fgn fs'') [0..< m]" (is "?xs = ?ys")
  proof (intro nth_equalityI, force, intro allI impI)
    fix j
    assume j: "j < length ?xs" 
    show "?xs ! j = ?ys ! j" 
    proof (cases "j = i \<or> j = i - 1")
      case True
      thus ?thesis using i i0 j by (cases "j = i", auto)
    next
      case other: False
      show ?thesis using j other by (simp add: swap(3), simp add: fs''[symmetric])
    qed
  qed
  finally have repr: "list_repr (i - 1) state' (map (fgn fs'') [0..< m])" .
  have "length fs'' = m" 
    using fs'' inv'(7) by auto
  hence fs_id: "fs'' = fs'" unfolding fs' of_list_repr[OF repr] fs_state_def
    by (intro nth_equalityI, auto simp: o_def)
  from repr fs_id have impl: "LLL_impl_inv state' (i - 1) fs'" 
    unfolding LLL_impl_inv_def by auto
  from swap(1-2) impl fs_id show ?g1 ?g2 ?g3 using res by auto
qed

lemma basis_reduction_step: assumes 
  impl: "LLL_impl_inv state i fs" 
  and inv: "LLL_invariant upw i fs" 
  and res: "basis_reduction_step \<alpha> upw i state = (upw',i',state')" 
  and i: "i < m" 
  and fs': "fs' = fs_state state'" 
shows 
  "LLL_impl_inv state' i' fs'" 
  "LLL_invariant upw' i' fs'" 
  "LLL_measure i' fs' < LLL_measure i fs" 
proof (atomize(full), goal_cases)
  case 1
  note def = basis_reduction_step_def
  from LLL_invD[OF inv] have len: "length fs = m" by auto
  from fs_state[OF impl len] have fs: "fs_state state = fs" by auto
  show ?case
  proof (cases "i = 0")
    case True
    from LLL_state_inc_i[OF impl inv i] i
      assms increase_i[OF inv i True] True 
      res fs' fs
    show ?thesis by (auto simp: def)
  next
    case False
    hence id: "(i = 0) = False" by auto
    obtain state'' where state'': "basis_reduction_add_rows upw state = state''" by auto
    define fs'' where fs'': "fs'' = fs_state state''" 
    from basis_reduction_add_rows[OF impl inv state'' i fs'']
    have inv: "LLL_invariant False i fs''"
      and meas: "LLL_measure i fs = LLL_measure i fs''" 
      and impl: "LLL_impl_inv state'' i fs''" by auto
    note res = res[unfolded def id if_False Let_def state'' 
        nim1_state[OF impl i False] ni_state[OF impl i]] 
    let ?x = "sq_norm (gso fs'' (i - 1))" 
    let ?y = "\<alpha> * sq_norm (gso fs'' i)" 
    show ?thesis
    proof (cases "?x \<le> ?y")
      case True
      from increase_i[OF inv i _ True] True res meas LLL_state_inc_i[OF impl inv i] fs' fs''
      show ?thesis by auto
    next
      case gt: False
      hence gt: "?x > ?y" and id: "(?x \<le> ?y) = False" by auto
      from res[unfolded id if_False] have "basis_reduction_swap i state'' = (upw', i', state')" by auto
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
    obtain i'' state'' upw'' where step: "basis_reduction_step \<alpha> upw i state = (upw'',i'',state'')" 
      (is "?step = _") by (cases ?step, auto)
    with res i have res: "basis_reduction_main \<alpha> m upw'' i'' state'' = state'" by auto
    note main = basis_reduction_step[OF impl inv step i refl]
    from IH[OF main(3,1,2) res]
    show ?thesis by auto
  next
    case False
    from LLL_invD[OF inv] have len: "length fs = m" by auto
    from fs_state[OF impl len] have fs: "fs_state state = fs" by auto
    from False LLL_invD[OF inv] have i: "i = m" upw by auto
    with False res inv impl fs show ?thesis by (auto simp: fs')
  qed
qed

lemma initial_state: "LLL_impl_inv (initial_state n fs_init) 0 fs_init" 
proof -
  have id: "gram_schmidt n (RAT fs_init) = map (gso fs_init) [0..<m]" 
    using gs.main_connect[OF lin_dep, unfolded length_map, OF len refl] by auto
  show ?thesis unfolding initial_state_def Let_def LLL_impl_inv_def list_repr_def gram_schmidt_triv id
    by (simp, intro nth_equalityI, auto simp: len)
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

value (code) "reduce_basis 2 (map vec_of_list [[1,2,3],[4,5,6],[7,8,10]])" 
end