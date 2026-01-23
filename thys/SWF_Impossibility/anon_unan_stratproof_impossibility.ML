
signature ANON_UNAN_STRATPROOF_IMPOSSIBILITY =
sig

exception PARSE

type ranking = int list
type sp_clauses = ranking list * ranking list * (ranking * ranking) list
val all_profiles : int -> int -> ranking list list

val generate_sat_problem :
  Proof.context -> thm -> int list list list -> sp_clauses list option -> 
  thm list -> SAT_Problem.T

type params = {
  name : string,
  locale_thm : thm,
  profile_file : Path.T option,
  sp_file : Path.T option,
  grat_file : Path.T,
  extra_clauses : thm list
}

val derive_false :
  Proof.context -> params -> thm

end


structure Anon_Unan_Stratproof_Impossibility : ANON_UNAN_STRATPROOF_IMPOSSIBILITY =
struct

open SWF_Util

type sat_problem = (int * cterm option array) * (int * (int list * thm) Array_Map.T)

fun multisetT T = Type (\<^type_name>\<open>multiset\<close>, [T])
fun multiset_empty T = Const (\<^const_name>\<open>zero_class.zero\<close>, multisetT T)
fun multiset_add_mset T = Const (\<^const_name>\<open>add_mset\<close>, T --> multisetT T --> multisetT T)

fun dest_multiset (Const (\<^const_name>\<open>zero_class.zero\<close>, Type (\<^type_name>\<open>multiset\<close>, _))) = []
  | dest_multiset (Const (\<^const_name>\<open>add_mset\<close>, _) $ t1 $ t2) = t1 :: dest_multiset t2
  | dest_multiset t = raise TERM ("dest_multiset", [t])

val profile_wf_simpset = simpset_of (put_simpset HOL_basic_ss @{context} addsimps
  @{thms size_add_mset size_empty eval_nat_numeral arith_simps refl HOL.simp_thms
         set_mset_add_mset_insert set_mset_empty mset.simps Set.ball_simps add_mset_commute})
val allowed_results_simpset = simpset_of (put_simpset HOL_basic_ss @{context} addsimps
  @{thms HOL.simp_thms if_False if_True list.set Int_insert_left Inter_empty
         Int_UNIV_right Int_empty_left Int_empty_right insert_iff empty_iff
         SWF_Impossibility_Automation.unanimity_def set_mset_add_mset_insert set_mset_empty image_insert
         image_empty Inter_insert list.map SWF_Impossibility_Automation.dom_set.simps topo_sorts_aux_Nil 
         topo_sorts_aux_Cons' filter.simps List.bind_simps prod.case fst_conv snd_conv
         Set_filter_empty Set_filter_insert_if append.simps insert_commute topo_sorts_aux_step_simps})

(*
  Computes all possible rankings on the given carrier set that are extensions of the given
  relation.
*)
fun toposort [] _ = [[]]
  | toposort xs rel =
      let
        val maxima = subtract op= (distinct op= (map fst rel)) xs
        fun rel' x = filter (fn (y,z) => y <> x andalso z <> x) rel
      in
        bind_list maxima (fn x =>
          map (fn zs => x :: zs) (toposort (remove op= x xs) (rel' x)))
      end 

(*
  Computes an explicit representation of the strict part of the linear order given by a ranking
  as a set of pairs.
*)
fun expand_ranking [] = []
  | expand_ranking (x :: xs) = map (fn y => (y,x)) xs @ expand_ranking xs

fun expand_ranking' ys = map_range (fn x => take_prefix (fn y => y <> x) ys) (length ys)

(*
  Computes the set of possible result rankings for the given profile allowed by unanimity.
*)
fun allowed_results profile =
  let
    val rel = fold1 (inter op=) (map expand_ranking profile)
  in
    toposort (hd profile) rel
  end


type profile =
  {id : int,
   const : cterm,
   wf_thm : thm,
   profile : int list list,
   allowed_results : int list list,
   allowed_results_thm : thm}

type ranking = int list
type literal = profile * ranking * bool
type clause = literal list
type sp_clauses = ranking list * ranking list * (ranking * ranking) list

fun all_profiles m n = multisets_of_length n (permutations (0 upto (m-1)))

structure Unanimitytab =
  Table (
    type key = int list list
    val ord = dict_ord (dict_ord int_ord)
  )

fun generate_sat_problem ctxt locale_thm profs sp_clauses extra_clauses =
  let
    val profs = distinct op= profs
    val (t_agents, t_alts, t_swf, t_agent_card, t_alts_list) =
      case Thm.prop_of locale_thm of
        \<^const>\<open>Trueprop\<close> $ (Const (\<^const_name>\<open>anonymous_unanimous_kemenysp_swf_explicit\<close>, _) $
           t_agents $ t_alts $ t_swf $ t_agent_card $ t_alts_list) =>
             (t_agents, t_alts, t_swf, t_agent_card, t_alts_list)
      | _ => raise THM ("generate_sat_problem", 1, [locale_thm])
    val alts = HOLogic.dest_list t_alts_list
    val m = length alts
    val altT = t_alts_list |> fastype_of |> dest_Type_args |> hd
    val agentT = t_agents |> fastype_of |> dest_Type_args |> hd
    val [cagentT, caltT] = map (Thm.ctyp_of ctxt) [agentT, altT]
    val [ct_agents, ct_alts, ct_swf, ct_agent_card, ct_alts_list] =
      map (Thm.cterm_of ctxt) [t_agents, t_alts, t_swf, t_agent_card, t_alts_list]
    val t_aswf =
       \<^instantiate>\<open>agents = t_agents and alts = t_alts and swf = t_swf and 'a = altT and 'b = agentT
         in term "anonymous_swf.aswf' (agents :: 'b set) (alts :: 'a set) swf"\<close>
    val n_agents = t_agent_card |> HOLogic.dest_number |> snd

    val calts_array = Array.fromList (map (Thm.cterm_of ctxt) alts)
    fun mk_calt i = Array.nth calts_array i
    val mk_alt = Thm.term_of o mk_calt
    val rankingT = HOLogic.listT altT
    val n_rankings = fact m
    val alts_distinct_thms = 
      (locale_thm RS @{thm anonymous_unanimous_kemenysp_swf_explicit.distinct_alts_list})
      |> mk_distinct_thms ctxt
    fun profile_to_nat [] = 0
      | profile_to_nat (r :: rs) = ranking_to_nat r + n_rankings * profile_to_nat rs

    fun term_to_alt t = 
      let
        val i = find_index (fn t' => t aconv t') alts
      in
        if i < 0 then raise TERM("term_to_alt", [t]) else i
      end
    
    local
      fun analyze_clause thm =
        let
          val analyze_profile = dest_multiset #> map (HOLogic.dest_list #> map term_to_alt)
          val analyze_ranking = HOLogic.dest_list #> map term_to_alt
          fun analyze_atom (Const (\<^const_name>\<open>HOL.eq\<close>, _) $ (f $ p) $ r) =
                if f aconv t_aswf then (analyze_profile p, analyze_ranking r)
                else raise THM ("analyze_clause", 1, [thm])
            | analyze_atom _ = raise THM ("analyze_clause", 1, [thm])
          fun analyze_lit (\<^const>\<open>Not\<close> $ atom) = let val (p, r) = analyze_atom atom in (p, r, false) end
            | analyze_lit atom = let val (p, r) = analyze_atom atom in (p, r, true) end
          fun collect_lits (\<^const>\<open>HOL.disj\<close> $ lit $ rest) = analyze_lit lit :: collect_lits rest
            | collect_lits lit = [analyze_lit lit]
          val lits = collect_lits (thm |> Thm.prop_of |> HOLogic.dest_Trueprop)
        in
          (lits, thm)
        end
    in
      val extra_clauses = map analyze_clause extra_clauses
    end

    fun find_extra_profs () =
      let
        fun mk_proftab xs = Inttab.make_distinct (map (fn p => (profile_to_nat p, p)) xs)
        val extra_profs = mk_proftab (flat (map (fst #> map #1) extra_clauses))
        val extra_profs =
          case sp_clauses of
            NONE => extra_profs
          | SOME ss =>
              fold (fn (p1, p2, _) => fn t => 
                Inttab.join (K fst) (t, mk_proftab [p1, p2])) ss extra_profs
      in
        Inttab.join (K fst) (mk_proftab profs, extra_profs)
        |> Inttab.dest
        |> map snd
      end
    val profs = timeap_msg "Collecting profiles" find_extra_profs ()

    val n_profiles = length profs
    val _ =
      writeln ("Using " ^ Int.toString n_profiles ^ " profiles with " ^ Int.toString m ^
        " alternatives, " ^ Int.toString n_agents ^ " agents.")

    exception INTERNAL_INDEX of int
    exception INTERNAL_RANKING of ranking
    local
      val alts_nil = Const (\<^const_name>\<open>Nil\<close>, HOLogic.listT altT)
      val alts_cons = Const (\<^const_name>\<open>Cons\<close>,  altT --> HOLogic.listT altT --> HOLogic.listT altT)
      val empty = multiset_empty rankingT
      val add_mset = multiset_add_mset rankingT
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
      val cnat_array = Array.fromList (map (cert o HOLogic.mk_number HOLogic.natT) (0 upto (m*m)))
    in
      fun mk_cnat k = Array.sub (cnat_array, k)
        handle General.Subscript => raise INTERNAL_INDEX k
      fun mk_cranking xs = Array.sub (ranking_array, ranking_to_nat xs)
        handle General.Subscript => raise INTERNAL_RANKING xs
      fun mk_cnatlist xs = Array.sub (cnatlist_array, ranking_to_nat xs)
        handle General.Subscript => raise INTERNAL_RANKING xs
      val mk_ranking = Thm.term_of o mk_cranking
      fun mk_rankings [] = empty
        | mk_rankings (xs :: xss) = add_mset $ mk_ranking xs $ mk_rankings xss
    end

    fun var (profile : profile, ranking) = ranking_to_nat ranking + n_rankings * #id profile + 1
             
    val variables : cterm option array = Array.array (n_profiles * n_rankings + 1, NONE)
    fun mk_lit (p, r, b) = (if b then I else ~) (var (p, r))

    (* compute profiles *)
    local
      val cconsts = map (Thm.cterm_of ctxt o mk_rankings) profs
      val profile_wf_ctxt = put_simpset profile_wf_simpset ctxt
      val allowed_results_ctxt =
            put_simpset allowed_results_simpset ctxt addsimps alts_distinct_thms
      val ceq = \<^instantiate>\<open>'a = caltT in cterm "(=) :: 'a list \<Rightarrow> 'a list \<Rightarrow> bool"\<close>
      val cswf = \<^instantiate>\<open>agents = ct_agents and alts = ct_alts and swf = ct_swf and
                  'a = cagentT and 'b = caltT
           in cterm "anonymous_swf.aswf' agents alts swf"\<close>

      fun prove_wf ct =
        let
          val thm =
            \<^instantiate>\<open>agents = ct_agents and alts = ct_alts and swf = ct_swf and 
                 agent_card = ct_agent_card and alts_list = ct_alts_list and Rs = ct and
                 'a = cagentT and 'b = caltT
             in lemma "anonymous_unanimous_kemenysp_swf_explicit agents alts swf agent_card alts_list \<Longrightarrow>
                       (size Rs = agent_card \<and> (\<forall>R\<in>#Rs. mset R = mset alts_list)) \<Longrightarrow>
                       anonymous_swf.is_apref_profile' (agents :: 'a set) (alts :: 'b set) Rs"
              by (subst anonymous_unanimous_kemenysp_swf_explicit.is_apref_profile'_iff)\<close>
        in
          simp_discharge profile_wf_ctxt (locale_thm RS thm)
        end

      val unanimity_of = map expand_ranking' #> fold1 (map2 (inter op=)) #> map (sort int_ord)

      local
        fun prove_toposort_eq (unanimity : int list list) =
          let
            val unanimity' = flat (map_index (fn (i,xs) => map (fn x => (i,x)) xs) unanimity)
            val unanimity'' = Thm.cterm_of ctxt
              let
                fun f (i, xs) =  HOLogic.mk_prod (mk_alt i, HOLogic.mk_set altT (map mk_alt xs))
              in
                map_index f unanimity
                |> HOLogic.mk_list (HOLogic.mk_prodT (altT, HOLogic.mk_setT altT))
              end
            val results = toposort (0 upto (m-1)) unanimity' |> sort (dict_ord int_ord)
            val results' =
              results
              |> map mk_ranking
              |> HOLogic.mk_set (HOLogic.listT altT)
              |> Thm.cterm_of ctxt
            val goal =
              \<^instantiate>\<open>rel = unanimity'' and 'a = caltT and A = results'
              in cprop "set (topo_sorts_aux rel) = A"\<close>
          in
            simp_prove allowed_results_ctxt goal
          end
        val toposort_table =
              profs
              |> map unanimity_of
              |> Unanimitytab.make_set
              |> Unanimitytab.keys
              |> map (fn r => (r, prove_toposort_eq r))
              |> Unanimitytab.make
      in
        val get_toposort_thm = Unanimitytab.lookup toposort_table #> the
      end

      fun prove_allowed_results ((profile, ct), wf_thm) =
        let
          val results = allowed_results profile |> sort (dict_ord int_ord)
          val results' = 
            results |> map mk_ranking |> HOLogic.mk_set rankingT |> Thm.cterm_of ctxt

          val unanimity = map (sort int_ord) (fold1 (map2 (inter op=)) (map expand_ranking' profile))
          val unanimity' = Thm.cterm_of ctxt
            let
              fun f (i, xs) =  HOLogic.mk_prod (mk_alt i, HOLogic.mk_set altT (map mk_alt xs))
            in
              map_index f unanimity
              |> HOLogic.mk_list (HOLogic.mk_prodT (altT, HOLogic.mk_setT altT))
            end
          val eq_thm = 
            \<^instantiate>\<open>alts_list = ct_alts_list and R = ct and res = unanimity' 
                        and 'a = caltT  and A = results'
                        in lemma "SWF_Impossibility_Automation.unanimity alts_list R = res \<Longrightarrow>
                                  set (topo_sorts_aux res) = A \<Longrightarrow>
                                  set (topo_sorts_aux (SWF_Impossibility_Automation.unanimity alts_list R)) = A"
              by simp\<close>
          val eq_thm = eq_thm |> simp_discharge allowed_results_ctxt
          val eq_thm = Thm.implies_elim eq_thm (get_toposort_thm unanimity)

          val thm = 
            \<^instantiate>\<open>agents = ct_agents and alts = ct_alts and swf = ct_swf and 
                 agent_card = ct_agent_card and alts_list = ct_alts_list and 
                 R = ct and A = results' and
                'a = cagentT and 'b = caltT
             in lemma "anonymous_unanimous_kemenysp_swf_explicit agents alts swf agent_card alts_list \<Longrightarrow>
                       anonymous_swf.is_apref_profile' (agents :: 'a set) (alts :: 'b set) R \<Longrightarrow>
                       set (topo_sorts_aux (SWF_Impossibility_Automation.unanimity alts_list R)) = A \<Longrightarrow>
                       anonymous_swf.aswf' agents alts swf R \<in> A"
              by (hypsubst, subst anonymous_unanimous_kemenysp_swf_explicit.allowed_results_def [symmetric], 
                    assumption, rule anonymous_unanimous_kemenysp_swf_explicit.aswf'_in_allowed_results)\<close>
          val thm = Drule.implies_elim_list thm [locale_thm, wf_thm, eq_thm]
          val thm = Local_Defs.unfold ctxt @{thms insert_iff empty_iff HOL.simp_thms} thm
        in
            (results, thm)
        end

      fun mk_profile (id, (((rankings, ct), wf_thm), (allowed_results, allowed_results_thm))) =
        let
          val p =
           {id = id, const = ct, wf_thm = wf_thm, profile = rankings,
            allowed_results = allowed_results, allowed_results_thm = allowed_results_thm} : profile
          fun register_var ranking =
            let
              val cvar = Thm.apply (Thm.apply ceq (Thm.apply cswf ct)) (mk_cranking ranking)
            in
              Array.update (variables, var (p, ranking), SOME cvar)
            end
          val _ = map register_var allowed_results
        in
          p
        end

      fun prove_wf_thms () =
        cconsts
        |> chop_groups 500
        |> Par_List.map (map prove_wf)
        |> flat
      val wf_thms =
         timeap_msg "Proving profile well-formedness" prove_wf_thms ()
      fun prove_allowed_results' () =
        (profs ~~ cconsts ~~ wf_thms)
        |> chop_groups 400
        |> Par_List.map (map prove_allowed_results)
        |> flat
      val allowed_results =
         timeap_msg "Proving unanimity clauses" prove_allowed_results' ()           
      val profiles = map_index mk_profile (profs ~~ cconsts ~~ wf_thms ~~ allowed_results)
      val profile_map = Inttab.make (map (fn prof => (profile_to_nat (#profile prof), prof)) profiles)
    in
      val profiles = profiles
      fun get_profile p =
        case Inttab.lookup profile_map (profile_to_nat p) of
          NONE => raise Match
        | SOME p' => p'
    end

    (* compute strategyproofness clauses *)
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
      val stratproof_ctxt = ctxt addsimps (alts_distinct_thms)
      val add_mset = Thm.cterm_of ctxt (multiset_add_mset rankingT)

      fun prove_stratproof_clause (prof1 : profile) (prof2 : profile) (s1, s2) =
        let
          val [t] = subtract1 op= (#profile prof2) (#profile prof1)
          val [t'] = subtract1 op= (#profile prof1) (#profile prof2)
          val (s1', s2') = apply2 (map (fn x => find_index (fn y => y = x) t)) (s1, s2)
          val ((d1, d1_thm), (d2, d2_thm)) = apply2 mk_inversion_thm (s1', s2')
        in
          if d2 >= d1 then
            prove_stratproof_clause prof2 prof1 (s2, s1)
          else let
            val [ct_s1, ct_s2, ct, ct'] = map mk_cranking [s1, s2, t, t']
            val (ct_s1', ct_s2') = apply2 mk_cnatlist (s1', s2')
            val (ct_d1, ct_d2) = apply2 mk_cnat (d1, d2)
            val ct_prof1 = #const prof1
            val ct_prof2 = #const prof2
            val ct_prof1' = Thm.apply (Thm.apply add_mset ct') ct_prof1
            val ct_prof2' = Thm.apply (Thm.apply add_mset ct) ct_prof2
            val mset_eq_thm = prove_mset_eq ctxt (ct_prof1', ct_prof2')
  
            val thm =
              \<^instantiate>\<open>agents = ct_agents and alts = ct_alts and swf = ct_swf and 
                 agent_card = ct_agent_card and alts_list = ct_alts_list and 
                 R1 = \<open>#const prof1\<close> and R2 = \<open>#const prof2\<close> and d1 = ct_d1 and d2 = ct_d2 and
                 S1 = ct_s1 and S2 = ct_s2 and S1' = ct_s1' and S2' = ct_s2' and T = ct and T' = ct' and
                 'a = cagentT and 'b = caltT
              in 
                lemma "anonymous_unanimous_kemenysp_swf_explicit agents alts swf agent_card alts_list \<Longrightarrow>
                       anonymous_swf.is_apref_profile' (agents :: 'a set) (alts :: 'b set) R1 \<Longrightarrow>
                       anonymous_swf.is_apref_profile' (agents :: 'a set) (alts :: 'b set) R2 \<Longrightarrow>
                       inversion_number S1' = d1 \<Longrightarrow> inversion_number S2' = d2 \<Longrightarrow>
                       map (index T) S1 = S1' \<Longrightarrow> map (index T) S2 = S2' \<Longrightarrow>
                       add_mset T' R1 \<equiv> add_mset T R2 \<Longrightarrow> d2 < d1 \<Longrightarrow>
                       anonymous_swf.aswf' agents alts swf R1 \<noteq> S1 \<or> 
                       anonymous_swf.aswf' agents alts swf R2 \<noteq> S2"
                by (rule anonymous_unanimous_kemenysp_swf_explicit.kemeny_strategyproof_aswf'_aux)\<close>
            val thm =
              Drule.implies_elim_list thm
                [locale_thm, #wf_thm prof1, #wf_thm prof2, d1_thm, d2_thm, 
                 mk_mapidx_thm t s1, mk_mapidx_thm t s2, mset_eq_thm]
             |> simp_discharge stratproof_ctxt
          in
            (prof1, s1, prof2, s2, thm)
          end
        end

      fun mk_stratproof_clauses (prof1 : profile, prof2 : profile) =
        case subtract1 op= (#profile prof2) (#profile prof1) of
          [r] => bind_list (#allowed_results prof1) (fn s1 =>
                   map (fn s2 => prove_stratproof_clause prof1 prof2 (s1, s2))
                     (filter (fn s2 => swap_dist r s1 > swap_dist r s2) (#allowed_results prof2)))
          | _ => []

      fun mk_stratproof_clauses' () =
        case sp_clauses of
          NONE => par_bind_list profiles (fn prof1 =>
                    bind_list profiles (fn prof2 => mk_stratproof_clauses (prof1, prof2)))
        | SOME sp_clauses =>
            let
              val sp_clauses = bind_list sp_clauses
                (fn (p1, p2, xs) => 
                 let val (p1, p2) = apply2 get_profile (p1, p2)
                 in  map (fn (r1, r2) => (p1, p2, r1, r2)) xs
                 end)
            in
              sp_clauses
              |> chop_groups 1000
              |> Par_List.map (map (fn (p1,p2,r1,r2) => prove_stratproof_clause p1 p2 (r1,r2)))
              |> flat
            end

    in
      val stratproof_thms =
        timeap_msg "Proving strategyproofness clauses" mk_stratproof_clauses' ()
    end

    val _ = writeln ("Proved " ^ Int.toString (length stratproof_thms) ^ " strategyproofness clauses.")


    (* make extra clauses *)
    val extra_clauses =
      let
        fun prep_extra_clause (cl, thm) =
          (map (fn (p,r,b) => (get_profile p,r,b)) cl, thm)
      in
        extra_clauses |> map (prep_extra_clause)
      end

    (* make unanimity clauses *)
    val unanimity_clauses =
      let
        fun mk_allowed_results_clause p =
          (map (fn r => (p, r, true)) (#allowed_results p), #allowed_results_thm p)
      in
        profiles |> map (mk_allowed_results_clause)
      end

    (* make strategyproofness clauses *)
    val stratproof_clauses =
      let
        fun mk_stratproof_clause (p1, s1, p2, s2, thm) = ([(p1, s1, false), (p2, s2, false)], thm)
      in
        stratproof_thms |> map (mk_stratproof_clause)
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

        val clauses = flat [extra_clauses, unanimity_clauses, stratproof_clauses]
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
  grat_file : Path.T,
  extra_clauses : thm list
}

fun derive_false ctxt params =
  let
    val {name, locale_thm, profile_file, sp_file, grat_file, extra_clauses} = params
    val thy = Proof_Context.theory_of ctxt  
    val profiles =
      case profile_file of
        NONE => []
      | SOME f => read_profiles_file (f, Path.is_xz f)
    val sp_clauses = Option.map (fn f => read_sp_clauses_file (f, Path.is_xz f)) sp_file
    val sat as ({n_vars, vars, n_clauses, clauses}) =
      generate_sat_problem ctxt locale_thm profiles sp_clauses extra_clauses
  
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
