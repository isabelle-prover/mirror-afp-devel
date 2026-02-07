
signature MAJCONS_STRATPROOF_IMPOSSIBILITY =
sig

type ranking = int list
type sp_clauses = ranking list * ranking list * (ranking * ranking) list

val all_profiles : int -> int -> ranking list list

val generate_sat_problem :
  Proof.context -> thm -> int list list list -> sp_clauses list option -> SAT_Problem.T

type params = {
  name : string,
  locale_thm : thm,
  profile_file : Path.T option,
  sp_file : Path.T option,
  grat_file : Path.T
}

val derive_false :
  Proof.context -> params -> thm

end


structure Majcons_Stratproof_Impossibility : MAJCONS_STRATPROOF_IMPOSSIBILITY =
struct

open SWF_Util

type profile =
  {id : int,
   const : cterm,
   wf_thm : thm,
   profile : int list list,
   allowed_results : int list list,
   allowed_results_thm : thm}

val profile_wf_simpset = simpset_of (put_simpset HOL_basic_ss @{context} addsimps
  @{thms refl HOL.simp_thms set_mset_add_mset_insert set_mset_empty mset.simps list.pred_inject
         add_mset_commute prod.case list.map fst_conv snd_conv list.size})



fun majority_relation zss =
  let
    val carrier = sort int_ord (hd zss)
    val maj = majority_ord (map ord_of_ranking zss)
  in
    map (fn x => (x, 
      filter (fn z => z <> x andalso is_less_equal (maj (x,z))) carrier)) carrier
  end

fun linorder rel =
  let
    fun go acc [] = SOME (rev acc)
      | go acc rel =
          case filter (fn (_, ys) => ys = []) rel of
            [(x, _)] => 
              rel |> filter (fn (y, _) => y <> x)
                  |> map (apsnd (remove op= x))
                  |> go (x :: acc)
          | _        => NONE
  in
    go [] rel
  end

val all_rankings_simps =
  @{thms permutations_of_set_list_def permutations_of_set_aux_list_Nil
         permutations_of_set_aux_list_Cons List.bind_simps append.simps
         if_True if_False remove1.simps refl}

val all_rankings_simpset =
  (put_simpset HOL_basic_ss @{context} addsimps all_rankings_simps) |> simpset_of
  
val majority_rel_list_simps =
  @{thms majority_rel_list_aux.simps list.map fst_conv snd_conv
         mset.simps filter.simps list.size of_ranking_Cons of_ranking_Nil
         refl list.pred_inject list.set eval_nat_numeral add_Suc_right add_Suc
         insert_iff empty_iff HOL.simp_thms arith_simps if_True if_False mult_Suc
         mult_Suc_right mult_0 mult_0_right Suc_less_eq zero_less_Suc Nat.not_less0
         add_mset_commute}

val majority_rel_list_simpset =
  (put_simpset HOL_basic_ss @{context} addsimps majority_rel_list_simps) |> simpset_of

val case_nat_0_thm = @{lemma "case_nat a b 0 = a" by simp}
val case_nat_numeral_thm = @{lemma "case_nat a b (numeral n) = b (pred_numeral n)" by simp}

val stratproof_simps =
  @{thms list.map HOL.simp_thms prod.case if_True if_False nat.case Suc_less_eq zero_less_Suc Nat.not_less0
         set_simps insert_iff empty_iff refl less_numeral_simps less_num_simps le_num_simps One_nat_def
         zero_less_numeral more_arith_simps zero_less_one pred_numeral_simps list_update.simps
         list.size BitM.simps nth.simps plus_nat.add_Suc plus_nat.add_0 eval_nat_numeral}
  @ [case_nat_0_thm, case_nat_numeral_thm]

val stratproof_simpset =
  (put_simpset HOL_basic_ss @{context} addsimps stratproof_simps) |> simpset_of

fun all_profiles m n = lists_of_length n (permutations (0 upto (m-1)))

fun generate_sat_problem ctxt locale_thm profs sp_clauses =
  let
    val profs = distinct op= profs
    val (t_agents, t_alts, t_swf, t_agents_list, t_alts_list) =
      case Thm.prop_of locale_thm of
        \<^const>\<open>Trueprop\<close> $ (Const (\<^const_name>\<open>majcons_kstratproof_swf_explicit\<close>, _) $
           t_agents $ t_alts $ t_swf $ t_agents_list $ t_alts_list) =>
             (t_agents, t_alts, t_swf, t_agents_list, t_alts_list)
      | _ => raise THM ("generate_sat_problem", 1, [locale_thm])
    val alts = HOLogic.dest_list t_alts_list
    val agents = HOLogic.dest_list t_agents_list
    val m = length alts
    val n = length agents
    val altT = t_alts_list |> fastype_of |> dest_Type_args |> hd
    val agentT = t_agents_list |> fastype_of |> dest_Type_args |> hd
    val [cagentT, caltT] = map (Thm.ctyp_of ctxt) [agentT, altT]
    val [ct_agents, ct_alts, ct_swf, ct_agents_list, ct_alts_list] =
      map (Thm.cterm_of ctxt) [t_agents, t_alts, t_swf, t_agents_list, t_alts_list]
    val t_swf' =
       \<^instantiate>\<open>swf = t_swf and 'a = altT and 'b = agentT
         in term "social_welfare_function_explicit.swf' swf"\<close>

    exception INTERNAL_INDEX of int
    exception INTERNAL_RANKING of ranking
    exception INTERNAL_PROFILE of ranking list

    val calts_array = Array.fromList (map (Thm.cterm_of ctxt) alts)
    fun mk_calt i = Array.sub (calts_array, i)
      handle General.Subscript => raise INTERNAL_INDEX i
    val mk_alt = Thm.term_of o mk_calt

    val cagents_array = Array.fromList (map (Thm.cterm_of ctxt) agents)
    fun mk_cagent i = Array.sub (cagents_array, i)
      handle General.Subscript => raise INTERNAL_INDEX i
    val mk_agent = Thm.term_of o mk_cagent

    val rankingT = HOLogic.listT altT
    val n_rankings = fact m
    val alts_distinct_thms = 
      (locale_thm RS @{thm majcons_kstratproof_swf_explicit.distinct_alts_list_aux})
      |> mk_distinct_thms ctxt
    val agents_distinct_thms = 
      (locale_thm RS @{thm majcons_kstratproof_swf_explicit.distinct_agents_list_aux})
      |> mk_distinct_thms ctxt
    fun profile_to_nat [] = 0
      | profile_to_nat (r :: rs) = ranking_to_nat r + n_rankings * profile_to_nat rs

    fun find_extra_profs () =
      let
        fun mk_proftab xs = Inttab.make_distinct (map (fn p => (profile_to_nat p, p)) xs)
        val extra_profs =
          case sp_clauses of
            NONE => Inttab.empty
          | SOME ss =>
              fold (fn (p1, p2, _) => fn t => 
                Inttab.join (K fst) (t, mk_proftab [p1, p2])) ss Inttab.empty
      in
        Inttab.join (K fst) (mk_proftab profs, extra_profs)
        |> Inttab.dest
        |> map snd
      end
    val profs = timeap_msg "Collecting profiles" find_extra_profs ()

    val n_profiles = length profs
    val _ =
      writeln ("Using " ^ Int.toString n_profiles ^ " profiles with " ^ Int.toString m ^
        " alternatives, " ^ Int.toString n ^ " agents.")

    local
      val alts_nil = Const (\<^const_name>\<open>Nil\<close>, HOLogic.listT altT)
      val alts_cons = Const (\<^const_name>\<open>Cons\<close>,  altT --> HOLogic.listT altT --> HOLogic.listT altT)
      val rankings_nil = \<^instantiate>\<open>'a = altT in term "[] :: 'a list list"\<close>
      val rankings_cons = \<^instantiate>\<open>'a = altT in term "(#) :: 'a list \<Rightarrow> _"\<close>
      fun mk_ranking [] = alts_nil
        | mk_ranking (x :: xs) = alts_cons $ mk_alt x $ mk_ranking xs
      val cert = Thm.cterm_of ctxt
      val ranking_array = 
        (0 upto (n_rankings - 1))
        |> map (cert o mk_ranking o nat_to_ranking m)
        |> Array.fromList
      val cnatlist_array = 
        (0 upto (n_rankings - 1))
        |> map (cert o HOLogic.mk_list HOLogic.natT o 
             map (HOLogic.mk_number HOLogic.natT) o nat_to_ranking m)
        |> Array.fromList
      val cnat_array =
         Array.fromList (map (cert o HOLogic.mk_number HOLogic.natT)
           (0 upto (Int.max (m*m, n))))
    in
      fun mk_cnat k = Array.sub (cnat_array, k)
        handle General.Subscript => raise INTERNAL_INDEX k
      fun mk_cranking xs = Array.sub (ranking_array, ranking_to_nat xs)
        handle General.Subscript => raise INTERNAL_RANKING xs
      fun mk_cnatlist xs = Array.sub (cnatlist_array, ranking_to_nat xs)
        handle General.Subscript => raise INTERNAL_RANKING xs
      val mk_ranking = Thm.term_of o mk_cranking
      fun mk_rankings xs =
        let fun go [] = rankings_nil
              | go (xs :: xss) =
                  rankings_cons $ mk_ranking xs $ go xss
      in
        if length xs <> length agents then
          raise INTERNAL_PROFILE xs
        else
          go xs
      end
    end

    fun var (profile : profile, ranking) = ranking_to_nat ranking + n_rankings * #id profile + 1
             
    val variables : cterm option array = Array.array (n_profiles * n_rankings + 1, NONE)
    fun mk_lit (p, r, b) = (if b then I else ~) (var (p, r))

    (* compute profiles *)
    local
      val cconsts = map (Thm.cterm_of ctxt o mk_rankings) profs
      val profile_wf_ctxt = put_simpset profile_wf_simpset ctxt
      val ceq = \<^instantiate>\<open>'a = caltT in cterm "(=) :: 'a list \<Rightarrow> 'a list \<Rightarrow> bool"\<close>
      val cswf = \<^instantiate>\<open>swf = ct_swf and
                  'a = cagentT and 'b = caltT and agents = ct_agents and agents_list = ct_agents_list
           in cterm "social_welfare_function_explicit.swf' agents swf agents_list"\<close>

      fun prove_wf ct =
        let
          val thm =
            \<^instantiate>\<open>agents = ct_agents and alts = ct_alts and swf = ct_swf and 
                 agents_list = ct_agents_list and alts_list = ct_alts_list and Rs = ct and
                 'a = cagentT and 'b = caltT
             in lemma "majcons_kstratproof_swf_explicit agents alts swf agents_list alts_list \<Longrightarrow>
                       length Rs = length agents_list \<and> 
                       list_all (\<lambda>ys. mset ys = mset alts_list) Rs \<Longrightarrow>
                       linorder_election_explicit.prefs_from_rankings_wf (agents :: 'a set) (alts_list :: 'b list) Rs"
              by (subst majcons_kstratproof_swf_explicit.prefs_from_rankings_wf_iff)\<close>
        in
          simp_discharge profile_wf_ctxt (locale_thm RS thm)
        end

      val all_rankings = map rev (permutations (0 upto (m-1)))
      val ct_all_rankings =
        all_rankings
        |> map mk_ranking
        |> HOLogic.mk_list rankingT
        |> Thm.cterm_of ctxt
      val all_rankings_ctxt =
        put_simpset all_rankings_simpset ctxt addsimps alts_distinct_thms
      val all_rankings_thm =
         \<^instantiate>\<open>alts_list = ct_alts_list and yss = ct_all_rankings and
                     'a = caltT in cprop "permutations_of_set_list alts_list = (yss :: 'a list list)"\<close>
         |> simp_prove all_rankings_ctxt        

      val majority_rel_list_ctxt =
        put_simpset majority_rel_list_simpset ctxt addsimps alts_distinct_thms
      fun compute_allowed ((rankings, ct), wf_thm) =
        case linorder (majority_relation rankings) of
          NONE =>
            let
              val thm =
                \<^instantiate>\<open>agents = ct_agents and alts = ct_alts and swf = ct_swf and
                            R = ct and yss = ct_all_rankings and alts_list = ct_alts_list and
                            agents_list = ct_agents_list and 'a = cagentT and 'b = caltT
                 in lemma "majcons_kstratproof_swf_explicit agents alts swf agents_list alts_list \<Longrightarrow>
                           linorder_election_explicit.prefs_from_rankings_wf (agents :: 'a set) (alts_list :: 'b list) R \<Longrightarrow>
                           permutations_of_set_list alts_list = yss \<Longrightarrow>
                           list_ex (\<lambda>ys. social_welfare_function_explicit.swf' agents swf agents_list R = ys) yss"
                 by (rule majcons_kstratproof_swf_explicit.swf'_in_all_rankings)\<close>
              val thm = Drule.implies_elim_list thm [locale_thm, wf_thm, all_rankings_thm]
                        |> Local_Defs.unfold ctxt @{thms list_ex_Nil_iff list_ex_Cons_iff HOL.simp_thms}
            in
              (all_rankings, thm)
            end
        | SOME ys =>
            let
              val thm =
                \<^instantiate>\<open>agents = ct_agents and alts = ct_alts and swf = ct_swf and
                                xss = ct and ys = \<open>mk_cranking ys\<close> and alts_list = ct_alts_list and
                                agents_list = ct_agents_list and 'a = cagentT and 'b = caltT
                     in lemma "majcons_kstratproof_swf_explicit agents alts swf agents_list alts_list \<Longrightarrow>
                               linorder_election_explicit.prefs_from_rankings_wf (agents :: 'a set) (alts_list :: 'b list) xss \<Longrightarrow>
                               mset ys = mset alts_list \<and> majority_rel_list_aux xss ys \<Longrightarrow>
                               social_welfare_function_explicit.swf' agents swf agents_list xss = ys"
                  by (rule majcons_kstratproof_swf_explicit.majority_consistent_swf'_aux; simp)\<close>
              val thm = Drule.implies_elim_list thm [locale_thm, wf_thm]
                        |> simp_discharge majority_rel_list_ctxt
            in
              ([ys], thm)
            end

      fun mk_profile (id, (((rankings, ct), wf_thm), (allowed, allowed_thm))) =
        let
          val p =
           {id = id, const = ct, wf_thm = wf_thm, profile = rankings,
            allowed_results = allowed, allowed_results_thm = allowed_thm} : profile
          fun register_var ranking =
            let
              val cvar = Thm.apply (Thm.apply ceq (Thm.apply cswf ct)) (mk_cranking ranking)
            in
              Array.update (variables, var (p, ranking), SOME cvar)
                handle General.Subscript => raise INTERNAL_INDEX (var (p, ranking))
            end
          val _ = map register_var allowed
        in
          p
        end

      fun prove_wf_thms () =
        cconsts
        |> chop_groups 500 |> Par_List.map (map prove_wf) |> flat
      val wf_thms = timeap_msg "Proving profile well-formedness" prove_wf_thms ()          
      fun prove_allowed_thms () = 
        (profs ~~ cconsts ~~ wf_thms) 
        |> chop_groups 200 |> Par_List.map (map compute_allowed) |> flat
      val allowed = timeap_msg "Proving allowed results for each profile" prove_allowed_thms ()
      val profiles = map_index mk_profile (profs ~~ cconsts ~~ wf_thms ~~ allowed)
      val profile_map = Inttab.make (map (fn prof => (profile_to_nat (#profile prof), prof)) profiles)
    in
      val profiles = profiles
      fun get_profile p =
        case Inttab.lookup profile_map (profile_to_nat p) of
          NONE => raise Match
        | SOME p' => p'
    end

    local
      (* cache for theorems of the form "inversion_number xs = n" where xs is a ranking *)
      val inversion_cache = mk_inversion_cache ctxt m
      fun mk_inversion_thm xs = Array.sub (inversion_cache, ranking_to_nat xs)

      (* cache for theorems of the form "index xs y = i", where xs is a ranking *)
      val idx_cache =
        let
          val idx_ctxt = ctxt addsimps alts_distinct_thms
          fun f j =
            let
              val (xs, y) = (nat_to_ranking m (j div m), j mod m)
              val i = find_index (fn x => x = y) xs
              val goal =
                \<^instantiate>\<open>xs = \<open>mk_cranking xs\<close> and y = \<open>mk_calt y\<close> and i = \<open>mk_cnat i\<close> and 'a = caltT in
                cprop "index xs (y :: 'a) = i"\<close>
            in
              simp_prove idx_ctxt goal
            end
        in
          Array.fromList (map f (0 upto (n_rankings * m - 1)))
        end

      (* efficiently prove theorem of the form "map (index xs) ys = zs" *)
      fun mk_mapidx_thm xs ys =
        let
          fun go xs [] _ _ _ = 
            \<^instantiate>\<open>xs = \<open>mk_cranking xs\<close> and 'alt = caltT in
              lemma "map (index xs) ([] :: 'alt list) = []" by simp\<close>
          | go xs (y :: ys) (z :: zs) ct_ys ct_zs =
              let
                val (ct_ys, ct_zs) = apply2 Thm.dest_arg (ct_ys, ct_zs)
                val thm1 = Array.sub (idx_cache, ranking_to_nat xs * m + y)
                val thm2 = go xs ys zs ct_ys ct_zs
                val thm3 =
                  \<^instantiate>\<open>xs = \<open>mk_cranking xs\<close> and ys = ct_ys and y = \<open>mk_calt y\<close> and
                              z = \<open>mk_cnat z\<close> and zs = ct_zs and 'alt = caltT in
                    lemma "index xs y = z \<Longrightarrow> map (index xs) ys = zs \<Longrightarrow> 
                             map (index xs) ((y::'alt) # ys) = z # zs"
                    by simp\<close>
              in
                Drule.implies_elim_list thm3 [thm1, thm2]
              end
          val zs = map (fn x => find_index (fn y => y = x) xs) ys
        in
          go xs ys zs (mk_cranking ys) (mk_cnatlist zs)
        end

      fun swap_dist xs ys =
        map (fn x => find_index (fn y => y = x) xs) ys |> mk_inversion_thm |> fst

      val stratproof_ctxt = put_simpset stratproof_simpset ctxt
      exception SP_CLAUSE of ranking list * ranking list * (ranking * ranking) option
      fun prove_sp (p1 : profile, p2 : profile, i, s1, s2) =
        let
          val t1 = List.nth (#profile p1, i)
          val t2 = List.nth (#profile p2, i)
          val (s1', s2') = apply2 (map (fn x => find_index (fn y => y = x) t1)) (s1, s2)
          val ((d1, d1_thm), (d2, d2_thm)) = apply2 mk_inversion_thm (s1', s2')
        in
          if d1 <= d2 then raise SP_CLAUSE (#profile p1, #profile p2, SOME (s1, s2))
          else
        let
          val thm = \<^instantiate>\<open>
            agents = ct_agents and alts = ct_alts and xss = \<open>#const p1\<close> and yss = \<open>#const p2\<close> and
            agents_list = ct_agents_list and alts_list = ct_alts_list and swf = ct_swf and
            'a = cagentT and 'b = caltT and i = \<open>mk_cnat i\<close> and ys = \<open>mk_cranking t1\<close> and
            zs = \<open>mk_cranking t2\<close> and d1 = \<open>mk_cnat d1\<close> and d2 = \<open>mk_cnat d2\<close> and
            S1 = \<open>mk_cranking s1\<close> and S2 = \<open>mk_cranking s2\<close> and
            S1' = \<open>mk_cnatlist s1'\<close> and S2' = \<open>mk_cnatlist s2'\<close>
            in lemma "majcons_kstratproof_swf_explicit (agents :: 'a set) (alts :: 'b set) swf agents_list alts_list \<Longrightarrow>
                      linorder_election_explicit.prefs_from_rankings_wf agents alts_list xss \<Longrightarrow> 
                      linorder_election_explicit.prefs_from_rankings_wf agents alts_list yss \<Longrightarrow>
                      map (index ys) S1 = S1' \<Longrightarrow> map (index ys) S2 = S2' \<Longrightarrow>
                      inversion_number S1' = d1 \<Longrightarrow> inversion_number S2' = d2 \<Longrightarrow> 
                      d1 > d2 \<and> i < length agents_list \<and> ys = xss ! i \<and> yss = xss[i := zs] \<Longrightarrow>
                      social_welfare_function_explicit.swf' agents swf agents_list xss \<noteq> S1 \<or> 
                      social_welfare_function_explicit.swf' agents swf agents_list yss \<noteq> S2"
              by (rule majcons_kstratproof_swf_explicit.kemeny_strategyproof_swf'_aux)\<close>
          val thm =
            Drule.implies_elim_list thm
              [locale_thm, #wf_thm p1, #wf_thm p2, mk_mapidx_thm t1 s1, mk_mapidx_thm t1 s2,
               d1_thm, d2_thm]
            |> simp_discharge stratproof_ctxt
        in
          (p1, p2, i, s1, s2, thm)
        end
        end

      fun prove_sp_permissive (p1, p2, i, s1, s2) =
        prove_sp (p1, p2, i, s1, s2)
          handle SP_CLAUSE ex => (
            prove_sp (p2, p1, i, s2, s1)
              handle SP_CLAUSE _ => raise SP_CLAUSE ex)

      fun differing_indices (p1 : profile, p2 : profile) =
        ((0 upto (n - 1)) ~~ #profile p1 ~~ #profile p2)
        |> map_filter (fn ((i,r1),r2) => if r1 <> r2 then SOME i else NONE)

      fun prove_sp' (p1 : profile, p2 : profile) =
        case differing_indices (p1, p2) of 
          [i] => 
            let
              val t = List.nth (#profile p1, i)
            in
              maps (fn s1 => maps (fn s2 =>
                 if swap_dist t s1 <= swap_dist t s2 then []
                 else [prove_sp (p1, p2, i, s1, s2)])
               (#allowed_results p2)) (#allowed_results p1)
            end
        | _ => []

     fun prove_sp_clauses () =
       case sp_clauses of
         NONE => par_bind_list profiles (fn p1 => bind_list profiles (fn p2 => prove_sp' (p1, p2)))
       | SOME sp_clauses =>
          let
            val sp_clauses = bind_list sp_clauses
              (fn (p1, p2, xs) => 
               let 
                 val (p1, p2) = apply2 get_profile (p1, p2)
               in
                 case differing_indices (p1, p2) of
                   [i] => map (fn (r1, r2) => (p1, p2, i, r1, r2)) xs
                 | _ => raise SP_CLAUSE (#profile p1, #profile p2, NONE)
               end)
          in
            sp_clauses
            |> chop_groups 1000
            |> Par_List.map (map prove_sp_permissive)
            |> flat
          end

    in
      val sp_clauses = timeap_msg "Proving strategyproofness clauses" prove_sp_clauses ()
    end

    (* profile clauses *)
    val profile_clauses =
      let
        fun mk_profile_clause p =
           (map (fn rs => (p, rs, true)) (#allowed_results p), #allowed_results_thm p)
      in
        profiles |> map mk_profile_clause
      end

    (* make strategyproofness clauses *)
    val sp_clauses =
      let
        fun mk_sp_clause (p1, p2, _, s1, s2, thm) = ([(p1, s1, false), (p2, s2, false)], thm)
      in
        sp_clauses |> map mk_sp_clause
      end


    fun consolidate_clauses () =
      let
        val cnot = \<^cterm>\<open>Not\<close>
        val ctrueprop = \<^cterm>\<open>Trueprop\<close>
        val cdisj = \<^cterm>\<open>(\<or>)\<close>
        fun mk_clit (p, r, true) = the (Array.sub (variables, var (p, r)))
          | mk_clit (p, r, false) = Thm.apply cnot (mk_clit (p, r, true))
        fun mk_cclause cl =
          let
            fun go [] = raise Empty
              | go [lit] = mk_clit lit
              | go (lit :: cl) = Thm.apply (Thm.apply cdisj (mk_clit lit)) (go cl)
          in
            Thm.apply ctrueprop (go cl)
          end

        val clauses = flat [profile_clauses, sp_clauses]
        val n_clauses = length clauses
        val clause_array = Array_Map.empty (n_clauses + 1)
        fun register_clause (i, (cl, thm)) =
           let
             val cprop = mk_cclause cl
             val thm' = Thm.implies_elim (Thm.trivial cprop) thm
           in
             Array_Map.update (clause_array, i+1, SOME (map mk_lit cl, thm'))
           end
        val _ = map_index register_clause clauses
      in
        (clause_array, n_clauses)
      end

    val (clause_array, n_clauses) =
      timeap_msg "Consolidating clauses" consolidate_clauses ()

  in {
       n_vars = n_profiles * n_rankings,
       vars = variables,
       n_clauses = n_clauses,
       clauses = clause_array
     }
  end

type params = {
  name : string,
  locale_thm : thm,
  profile_file : Path.T option,
  sp_file : Path.T option,
  grat_file : Path.T
}

fun derive_false ctxt (params : params) =
  let
    val {name, locale_thm, profile_file, sp_file, grat_file} = params
    val thy = Proof_Context.theory_of ctxt  
    val profiles =
      case profile_file of
        NONE => []
      | SOME f => read_profiles_file (f, Path.is_xz f)
    val sp_clauses = Option.map (fn f => read_sp_clauses_file (f, Path.is_xz f)) sp_file
    val sat as ({n_vars, vars, n_clauses, clauses}) =
      generate_sat_problem ctxt locale_thm profiles sp_clauses
  
    val _ =
      writeln ("Generated SAT problem has " ^ Int.toString n_vars ^ " variables, " ^
        Int.toString n_clauses ^ " clauses.")
  
    val path = Path.basic (name ^ ".cnf")
    val _ =
       let
         val dimacs = timeap_msg "Exporting to DIMACS" SAT_Problem.mk_dimacs sat
       in            
         Export.export thy (Path.binding (path, \<^here>)) (Bytes.contents_blob dimacs)
       end
    val _ = writeln (
      "DIMACS file stored in theory exports: " ^
        Markup.markup (Export.markup thy path) (name ^ ".cnf"))
  
    val rup_input = {
        ctxt = ctxt,
        tracing = false,
        n_vars = n_vars,
        vars = vars,
        clauses = clauses
      } : Replay_RUP.rup_input

    val thm =
      timeap_msg "Replaying RUP proof" (Replay_RUP.replay_rup_file rup_input)
        (grat_file, Path.is_xz grat_file)
  in
    thm
  end

end
