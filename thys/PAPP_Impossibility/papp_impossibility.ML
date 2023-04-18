(*
  File:     papp_impossibility.ML
  Author:   Manuel Eberl, University of Innsbruck

  This file implements the generation of a SAT problem in DIMACS format from the situation we
  have in the base case of the P-APP impossibility, and the replaying of an externally found
  GRAT proof to prove that impossibility.
*)

signature PAPP_IMPOSSIBILITY =
sig

type clause = int list * thm
type sat_problem = (int * cterm option array) * (int * clause Array_Map.T) * thm * Proof.context

val mk_sat_problem : Proof.context -> Path.T -> sat_problem
val mk_dimacs : sat_problem -> string
val write_dimacs : sat_problem -> Path.T -> unit
val replay_grat : Proof.context -> sat_problem -> Path.T -> thm
val derive_false : Proof.context -> Path.T -> Path.T -> thm

end


structure PAPP_Impossibility : PAPP_IMPOSSIBILITY =
struct

type clause = int list * thm
type sat_problem = (int * cterm option array) * (int * clause Array_Map.T) * thm * Proof.context

exception CLAUSE of cterm * thm

fun decode_approval_list i =
  let
    val i' = i + 1
  in
    filter (fn j => IntInf.andb (i', IntInf.<< (1, Word.fromInt j)) <> 0) (0 upto 3)
  end

fun mk_committees k n =
  let
    fun go (lo, hi, n) =
      if hi <= lo orelse n < 0 then []
      else if n = 0 then [[]]
      else map (fn xs => lo :: xs) (go (lo, hi, n-1)) @ go (lo+1, hi, n)
  in
    go (0, k, n)
  end

fun ccand 0 = \<^cterm>\<open>C1\<close>
  | ccand 1 = \<^cterm>\<open>C2\<close>
  | ccand 2 = \<^cterm>\<open>C3\<close>
  | ccand 3 = \<^cterm>\<open>C4\<close>
  | ccand _ = raise Match

val cand = Thm.term_of o ccand

val candT = \<^typ>\<open>'a\<close>
val candsetT = HOLogic.mk_setT candT
fun mk_msetT T = Type (\<^type_name>\<open>Multiset.multiset\<close>, [T])
fun mk_empty_mset T = Const (\<^const_name>\<open>Groups.zero\<close>, mk_msetT T)
fun mk_add_mset T =
  let
    val T' = mk_msetT T
  in
    Const (\<^const_name>\<open>Multiset.add_mset\<close>, T --> T' --> T')
  end
val add_mset_cterm_candset' = \<^cterm>\<open>add_mset :: 'a set \<Rightarrow> _\<close>

val profileT = mk_msetT candsetT
val commT = mk_msetT candT

fun mk_mset T ts =
  let
    val empty = mk_empty_mset T
    val add = mk_add_mset T
    fun add' a b = add $ a $ b
  in
    fold_rev add' ts empty
  end

type profile = {id : int, profile : int list, cterm : cterm, wf_thm : thm}

val is_pref_profile_iff_thm = @{thm eq_reflection[OF is_pref_profile_iff]}

val profile_cterm = (#cterm : profile -> cterm)
val profile_term = Thm.term_of o profile_cterm

val eq_trueD = @{lemma "PROP P \<equiv> PROP Trueprop True \<Longrightarrow> PROP P" by simp}

fun simp_prove ctxt ct =
  let
    val thm = Simplifier.rewrite ctxt ct
    val rhs = thm |> Thm.cconcl_of |> Thm.dest_equals_rhs
  in
    if Thm.term_of rhs = \<^prop>\<open>True\<close> then
      Thm.implies_elim
        (Thm.instantiate (TVars.empty, Vars.make [((("P", 0), propT), ct)]) eq_trueD) thm
    else
      raise CTERM ("simp_prove: Failed to finish proof", [rhs])
  end

fun simp_discharge ctxt thm =
  let
    val prem = Thm.cprem_of thm 1
  in
    Thm.implies_elim thm (simp_prove ctxt prem)
  end

fun simp_discharge_all ctxt thm =
  if Thm.nprems_of thm = 0 then thm else simp_discharge_all ctxt (simp_discharge ctxt thm)

fun consolidate_hyps thms =
  let
    val thm = Conjunction.intr_balanced thms
    val thm' = Thm.assume (Thm.cprop_of thm)
    val thms' = Conjunction.elim_balanced (length thms) thm'
  in (thms', thm) end

val mset_swap_conv =
  Conv.rewr_conv @{thm eq_reflection[OF add_mset_commute]}

fun norm_profile_conv [] ct = Conv.all_conv ct
  | norm_profile_conv [_] ct = Conv.all_conv ct
  | norm_profile_conv (x :: y :: xs) ct =
      if x > y then
        (mset_swap_conv
         then_conv Conv.arg_conv (norm_profile_conv (x :: xs))) ct
      else
        Conv.all_conv ct

fun committee_score app (cs : int list) = length (filter (member op= app) cs)
fun committee_less app cs1 (cs2 : int list) = committee_score app cs1 < committee_score app cs2

fun group [] = []
  | group (x :: xs) =
      let
        fun go (x, n) [] acc = rev ((x, n) :: acc)
          | go (x, n) (y :: ys) acc =
              if x = y then go (x, n+1) ys acc else go (y, 1) ys ((x, n) :: acc)
      in
        go (x, 1) xs []
      end

fun pairs [] = []
  | pairs (x :: xs) = map (fn y => (x, y)) xs @ pairs xs

fun encode_var (i, j) = i * 20 + j + 1
fun encode_lit (b, i, j) =
  let val v = encode_var (i, j) in if b then ~v else v end
fun decode_var v = IntInf.divMod (v-1, 20)
fun decode_lit l = case decode_var (abs l) of (i, j) => (l < 0, i, j)

fun mk_disjs [] = raise Empty
  | mk_disjs [x] = x
  | mk_disjs (x :: xs) = HOLogic.mk_disj (x, mk_disjs xs)

fun rev_maps_pairs f xs =
  let
    fun go [] acc = acc
      | go (x :: xs) acc =
          let
            fun go' [] acc = acc
              | go' (y :: ys) acc = go' ys (f (x, y) @ acc)
          in
            go xs (go' xs acc)
          end
  in
    go xs []
  end

fun get_approval_list ct 0 = Thm.dest_arg1 ct
  | get_approval_list ct i = get_approval_list (Thm.dest_arg ct) (i - 1)

val not_manipulable_thm' =
  @{lemma "is_pref_profile A \<Longrightarrow> is_pref_profile B \<Longrightarrow> A' \<equiv> A \<Longrightarrow> B' \<equiv> B \<Longrightarrow> add_mset Y A \<equiv> add_mset X B \<Longrightarrow>
            \<not>r A \<prec>[Comm(X)] r B"
      by (rule not_manipulable'[of A B Y X]) auto}

val stratproof_aux_thm =
  @{lemma "\<not>r B \<succ>[Comm(X)] r A \<Longrightarrow> A' \<equiv> A \<Longrightarrow> B' \<equiv> B \<Longrightarrow> W \<prec>[Comm(X)] W' \<Longrightarrow> r A' \<noteq> W \<or> r B' \<noteq> W'" by blast}

fun add_mset_cterm_candset ct1 profile =
  Thm.apply (Thm.apply add_mset_cterm_candset' ct1) (profile_cterm profile)

fun prove_add_mset_eq (xs, ct1) (ys, ct2) =
  let
    val thm1 = norm_profile_conv xs ct1
    val thm2 = norm_profile_conv ys ct2
  in
    Thm.transitive thm1 (Thm.symmetric thm2)
  end

fun is_subset [] _ = true
  | is_subset _ [] = false
  | is_subset (x :: xs) (y :: ys) = (x = y andalso is_subset xs ys) orelse is_subset (x :: xs) ys

fun exists_index p xs =
  let
    fun go _ [] = false
      | go i (x :: xs) = p (i, x) orelse go (i + 1) xs
  in
    go 0 xs
  end



fun mk_sat_problem ctxt profiles_file =
let
  val committee_list = mk_committees 4 3
  val committees = Array.fromList committee_list
  fun committee i = Array.sub (committees, i)

  val approval_list_cache' =
    Array.tabulate (14, decode_approval_list #> map cand #> HOLogic.mk_set candT)

  val approval_list_cache =
    Array.tabulate (14, fn i => Thm.cterm_of ctxt (Array.sub (approval_list_cache', i)))

  fun holify_approval_list i = Array.sub (approval_list_cache, i)
  fun holify_approval_list' i = Array.sub (approval_list_cache', i)


  val holify_profile' =
    map holify_approval_list' #> mk_mset candsetT

  fun mk_profile ctxt id profile =
    let
      val term = holify_profile' profile
      val goal = \<^instantiate>\<open>A = "term" in prop \<open>is_pref_profile A\<close>\<close>
      val thm =
        Goal.prove ctxt [] [] goal
          (fn {context, ...} =>
             HEADGOAL (EqSubst.eqsubst_tac ctxt [0] [is_pref_profile_iff_thm]
             THEN_ALL_NEW Simplifier.simp_tac context))
      val cterm = thm |> Thm.cconcl_of |> Thm.dest_arg |> Thm.dest_arg
    in
      {id = id, profile = profile, cterm = cterm, wf_thm = thm} : profile
    end

  fun read_profiles ctxt path =
    let
      fun process_line (id, l) =
        l
        |> space_explode " "
        |> map (the o Int.fromString)
        |> mk_profile ctxt id
    in
      File.read_lines path
      |> filter (fn l => l <> "")
      |> map_index I
      |> chop_groups 50
      |> Par_List.map (map process_line)
      |> flat
    end

  val profs = read_profiles ctxt profiles_file
  val profile_array = Array.fromList profs

  local
    fun mk_def prof =
      ((Binding.make ("prof" ^ Int.toString (#id prof), \<^here>), NoSyn),
         (Binding.empty_atts, profile_term prof))
    val xs = map mk_def profs
    val (aux, ctxt) = Local_Defs.define xs ctxt
  in
    val ctxt' = ctxt
    val profile_consts = Array.fromList (map fst aux)
    val profile_defs = Array.fromList (map (snd o snd) aux)
    fun profile_const (prof : profile) = Array.sub (profile_consts, #id prof)
    fun profile_cconst (prof : profile) = Thm.cterm_of ctxt (profile_const prof)
    fun profile_def (prof : profile) = Array.sub (profile_defs, #id prof)
  end

  local
    fun mk_committee i =
      committee i
      |> map cand
      |> mk_mset candT
    fun mk_def i =
      ((Binding.make ("W" ^ Int.toString i, \<^here>), NoSyn),
         (Binding.empty_atts, mk_committee i))
    val xs = map_range mk_def 20
    val (aux, ctxt) = Local_Defs.define xs ctxt'
  in
    val ctxt' = ctxt
    val w_consts = Array.fromList (map (Thm.cterm_of ctxt' o fst) aux)
    val w_def_list = map (snd o snd) aux
    val w_def_list_sym = map Thm.symmetric w_def_list
  end

  fun holify_committee i = Array.sub (w_consts, i)
  val holify_committee' = holify_committee #> Thm.term_of

  fun mk_committee_pref_thms app =
    let
      val ctxt'' = ctxt' addsimps (w_def_list @ @{thms strongly_preferred_def committee_preference_def})
      val n = Array.length committees
      val app' = decode_approval_list app
      fun mk' (c1, c2) =
        let
          val goal =
            \<^instantiate>\<open>X = "holify_committee' c1" and Y = "holify_committee' c2"
              and A = "holify_approval_list' app"
              in prop \<open>X \<prec>[Comm(A)] Y\<close>\<close>
          fun tac ctxt = Simplifier.simp_tac ctxt
        in
          (c1, c2, Goal.prove ctxt'' [] [] goal (fn {context, ...} => HEADGOAL (tac context)))
        end
      fun mk (c1, c2) acc =
        if committee_less app' (committee c1) (committee c2) then
          mk' (c1, c2) :: acc
        else
          acc
    in
      fold_range (fn i => fold_range (fn j => mk (i, j)) n) n [] |> rev
    end

  val committee_pref_cache =
    (0 upto 14) |> Par_List.map mk_committee_pref_thms |> Array.fromList

  fun weak_rep ctxt (profiles : profile list) =
    let
      val n_committees = Array.length committees
      val subtract = fold (remove1 op=)
      datatype elim = Weak_Rep | Lemma of int
      fun sing_alts (profile : profile) =
        #profile profile
        |> map_filter (fn i => case decode_approval_list i of [x] => SOME x | _ => NONE)
        |> sort int_ord
        |> group
        |> filter (fn (_, n) => n >= 2)
        |> map fst
      val ctxt'' = ctxt addsimps w_def_list

      (*
        Returns a list of all committees that are forbidden for the given profile due to
        weak representation, and why they are forbidden (basic WP or the Lemma).
        Additionally, the set of candidates forced into the committee by WP is also returned.
      *)
      fun elims profile =
        let
          val sings = sing_alts profile
          val ws = 0 upto (n_committees - 1)

          fun upd (idx, i) (ws, acc)=
            let
              val xs = decode_approval_list i
              fun suitable (idx', j) =
                idx <> idx' andalso
                let
                  val ys = decode_approval_list j
                in
                  subset op= (ys, xs) andalso
                  not (subset op= (ys, sings))
                end
            in
              if exists_index suitable (#profile profile) then
                let
                  val es =
                    filter_out (fn w => exists (member op= xs) (subtract sings (committee w))) ws
                in
                  (subtract es ws, if null es then acc else (es, Lemma i) :: acc)
                end
              else
                (ws, acc)
            end

          val es = filter_out (fn w => is_subset sings (committee w)) ws
          val state = (subtract es ws, if null es then [] else [(es, Weak_Rep)])
          val state = fold_index upd (#profile profile) state
        in
          (sings, fst state, snd state)
        end

      fun mk_clauses (profile, (sings, remaining, justifications)) =
        let
          val sings_cterm = Thm.cterm_of ctxt (HOLogic.mk_set candT (map cand sings))
          val goal =
             \<^instantiate>\<open>A = "profile_cterm profile" and Z = sings_cterm
               in cprop \<open>\<forall>x\<in>Z. count A {x :: 'a} \<ge> 2\<close>\<close>
          val sing_thm = simp_prove ctxt'' goal

          fun mk_clauses' (ws, Weak_Rep) =
                let
                  fun go w =
                    let
                      val insts = [((("W", 0), commT), holify_committee w)]
                      val rule = Thm.instantiate (TVars.empty, Vars.make insts) @{thm weak_representation'}
                      val thm =
                        (rule OF [#wf_thm profile, profile_def profile, sing_thm])
                        |> simp_discharge_all ctxt''
                    in
                      thm
                    end
                 in
                   map go ws
                 end
           | mk_clauses' (ws, Lemma i) =
                let
                  fun go w =
                    let
                      val insts =
                        [((("X", 0), candsetT), holify_approval_list i),
                         ((("W", 0), commT), holify_committee w)]
                      val rule = Thm.instantiate (TVars.empty, Vars.make insts) @{thm lemma2''}
                      val thm =
                        (rule OF [#wf_thm profile, profile_def profile, sing_thm])
                        |> simp_discharge_all ctxt''
                    in
                      thm
                    end
                 in
                   map go ws
                 end
        in
          (remaining, maps mk_clauses' justifications)
        end

    in
      profiles |> chop_groups 10 |> Par_List.map (map (fn profile => mk_clauses (profile, elims profile))) |> flat
    end

  local
    val _ = writeln "Generating weak representation facts..."
    val start = Timing.start ()
    val wrs = weak_rep ctxt profs
    val _ = writeln (Timing.message (Timing.result start))
  in
    val possible_committee_table = Array.fromList (map (Inttab.make_set o fst) wrs)
    val wr_thm_table = Array.fromList (map snd wrs)
    fun is_possible_committee (p : profile, i : int) =
      Inttab.defined (Array.sub (possible_committee_table, #id p)) i
  end

  val n_vars = Array.length committees * length profs
  val vars =
     Array.tabulate (n_vars + 1,
       fn v => if v = 0 then NONE else SOME (
         let val (i, j) = decode_var v
         in \<^instantiate>\<open>
              A = "profile_const (Array.sub (profile_array, i))" and W = "holify_committee' j"
              in term \<open>r A = W\<close>\<close> |> Thm.cterm_of ctxt
         end))
  fun get_var (profile : profile, i) =
    the (Array.sub (vars, encode_var (#id profile, i)))
  val get_var' = Thm.term_of o get_var

  fun total_conv wr_thms =
    let
      val neg_imp_eq_False_thm = @{lemma "\<not>P \<Longrightarrow> P \<equiv> False" by simp}
      val reduce_thms = @{lemma "False \<or> P \<equiv> P" and "P \<or> False \<equiv>  P" by simp_all}
      val thms = reduce_thms @ map (fn thm => thm RS neg_imp_eq_False_thm) wr_thms
    in
      Conv.bottom_conv (K (Conv.repeat_conv (Conv.rewrs_conv thms))) ctxt'
    end

  fun functional profiles =
    let
      val unfold_thms = map (fn thm => thm RS @{thm eq_reflection})
         @{thms COM'_def pairs.simps list_ex_unfold list_all_unfold list.map append.simps prod.case}
      val r_in_com_thm =
        @{thm r_in_COM'}
        |> Local_Defs.unfold ctxt' (unfold_thms @ w_def_list_sym)
      val r_right_unique_thm =
        @{thm r_right_unique}
        |> Local_Defs.unfold ctxt' (unfold_thms @ w_def_list_sym)
      val n = Array.length committees
      val committee_pairs = pairs (0 upto (n - 1))
      fun mk_clause (profile : profile) =
        let
          val id = #id profile
          val insts = [((("A", 0), profileT), profile_cterm profile),
                       ((("A'", 0), profileT), Thm.cterm_of ctxt' (profile_const profile))] |> Vars.make
          val inst = Thm.instantiate (TVars.empty, insts)
          val insts' = [((("A", 0), profileT), Thm.cterm_of ctxt' (profile_const profile))] |> Vars.make
          val inst' = Thm.instantiate (TVars.empty, insts')

          val possible =
            Inttab.keys (Array.sub (possible_committee_table, id))
          val total_clause = map (fn i => (false, id, i)) possible
          val wr_thms = Array.sub (wr_thm_table, id)
          val total_thm =
            inst r_in_com_thm
            |> Thm.elim_implies (#wf_thm profile)
            |> Thm.elim_implies (profile_def profile)
            |> Conv.fconv_rule (Conv.arg_conv (total_conv wr_thms))
          val right_unique_thms = inst' r_right_unique_thm |> HOLogic.conj_elims ctxt
          val right_unique_clauses =
            (committee_pairs ~~ right_unique_thms)
            |> filter (fn ((i, j), _) => is_possible_committee (profile, i)
                 andalso is_possible_committee (profile, j))
            |> map (apfst (fn (i, j) => [(true, id, i), (true, id, j)]))
        in
          (total_clause, total_thm) :: right_unique_clauses
        end
    in
      profiles |> chop_groups 200 |> Par_List.map (map mk_clause) |> flat |> flat
    end

  val _ = writeln "Generating totality and right-uniqueness facts..."
  val start = Timing.start ()
  val functional_clauses = functional profs
  val _ = writeln (Timing.message (Timing.result start))

  val symm_break_thm =
    @{lemma "r ({#{C1}, {C2}, {C1, C2}, {C3}, {C4}, {C3, C4}#}) = {#C1, C1, C3#} \<or>
             r ({#{C1}, {C2}, {C1, C2}, {C3}, {C4}, {C3, C4}#}) = {#C1, C2, C3#}"
         by (use symmetry_break in simp)}
    |> Local_Defs.fold ctxt' (Array.sub (profile_defs, 0) :: w_def_list)
  val symm_break_clauses = [([(false, 0, 2), (false, 0, 5)], symm_break_thm)]

  fun stratproof (profiles : profile list) =
    let
      val subtract = fold (remove1 op=)
      fun analyze_pair (p1, p2) =
        let
          val (xs, ys) = apply2 #profile (p1, p2)
        in
          case (subtract ys xs, subtract xs ys) of
            ([x], [y]) => [(p1, x, p2, y), (p2, y, p1, x)]
          | _ => []
        end
      val ps =
        profiles
        |> rev_maps_pairs analyze_pair
      fun mk_clauses (p1 : profile, x : int, p2 : profile, y : int) =
        let
          val x_idx = find_index (fn u => u = x) (#profile p1)
          val y_idx = find_index (fn u => u = y) (#profile p2)
          val x_cterm = get_approval_list (#cterm p1) x_idx
          val y_cterm = get_approval_list (#cterm p2) y_idx
          val insts =
            [("A", profileT, #cterm p1), ("B", profileT, #cterm p2),
             ("A'", profileT, profile_cconst p1), ("B'", profileT, profile_cconst p2),
             ("X", candsetT, x_cterm), ("Y", candsetT, y_cterm)]
          val vars =
            insts
            |> map (fn (s, T, t) => (((s, 0), T), t))
            |> Vars.make
          val eq_thm =
            prove_add_mset_eq
              (y :: #profile p1, add_mset_cterm_candset y_cterm p1)
              (x :: #profile p2, add_mset_cterm_candset x_cterm p2)
          val not_less_thm =
            not_manipulable_thm'
            |> Thm.instantiate (TVars.empty, vars)
            |> Thm.elim_implies (#wf_thm p1)
            |> Thm.elim_implies (#wf_thm p2)
            |> Thm.elim_implies (profile_def p1)
            |> Thm.elim_implies (profile_def p2)
            |> Thm.elim_implies eq_thm
          val comms = Array.sub (committee_pref_cache, x)
          fun mk_clause (c1, c2, less_thm) =
            if is_possible_committee (p1, c1) andalso is_possible_committee (p2, c2) then
              let
                val insts =
                  insts @ [("W", commT, holify_committee c1), ("W'", commT, holify_committee c2)]
                val vars =
                  insts
                  |> map (fn (s, T, t) => (((s, 0), T), t))
                  |> Vars.make
                val thm =
                  stratproof_aux_thm
                  |> Thm.instantiate (TVars.empty, vars)
                  |> Thm.elim_implies not_less_thm
                  |> Thm.elim_implies (profile_def p1)
                  |> Thm.elim_implies (profile_def p2)
                  |> Thm.elim_implies less_thm
              in
                [([(true, #id p1, c1), (true, #id p2, c2)], thm)]
              end
            else
              []
        in
          maps mk_clause comms
        end
    in
      ps
      |> chop_groups 1000
      |> Par_List.map (map mk_clauses)
      |> flat
      |> flat
    end

  val _ = writeln "Generating strategyproofness facts..."
  val start = Timing.start ()
  val sp_clauses = stratproof profs
  val _ = writeln (Timing.message (Timing.result start))

  fun prep (cs, thm) =
    (map encode_lit cs, Thm.transfer' ctxt' thm)

  val clauses = Array_Map.empty 1000000 : (int list * thm) Array_Map.T
  val add_clauses =
    fold (fn x => fn i =>
      let val _ = Array_Map.update (clauses, i + 1, SOME (prep x)) in i + 1 end)
(*  val n_clauses = fold add_clauses [symm_break_clauses, functional_clauses, sp_clauses] 0*)

  val _ = writeln "Consolidating theorems..."
  val start = Timing.start ()
  val clauses1 = maps (map fst) [symm_break_clauses, functional_clauses, sp_clauses]
  val (clauses2, hyp_thm) =
    consolidate_hyps (maps (map snd) [symm_break_clauses, functional_clauses, sp_clauses])
  val n_clauses = add_clauses (clauses1 ~~ clauses2) 0
  val _ = writeln (Timing.message (Timing.result start))

  local
    fun term_of_clause' cl =
      let
        fun term_of_var x = the (Array.sub (vars, x)) |> Thm.term_of
        fun term_of_lit x =
          if x < 0 then \<^const>\<open>HOL.Not\<close> $ term_of_var (abs x) else term_of_var (abs x)
        fun go [] = raise Empty
          | go [x] = term_of_lit x
          | go (x :: xs) = HOLogic.mk_disj (term_of_lit x, go xs)
      in
        go cl |> HOLogic.mk_Trueprop
      end

    fun check_clause' (cl, thm) =
      if Thm.prop_of thm = term_of_clause' cl then
        ()
      else
        raise CLAUSE (Thm.cterm_of ctxt (term_of_clause' cl), thm)

    fun check i = if i > n_clauses then () else
      let val _ = check_clause' (the (Array_Map.sub (clauses, i))) in check (i+1) end
  in
    val _ = writeln "Checking correctness of clauses..."
    val start = Timing.start ()
    val _ = check 1
    val _ = writeln (Timing.message (Timing.result start))
  end

  val n_vars =
    fold_range (fn i => fn a =>
      case Array_Map.sub (clauses, i) of
        SOME cl => fold (fn a => fn b => Int.max (abs a, b)) (fst cl) a
      | NONE => a) (n_clauses + 1) 0

in
  ((n_vars, vars), (n_clauses, clauses), hyp_thm, ctxt')
end


fun dimacs_gen st put ((n_vars, _), (n_clauses, clauses), _, _) =
  let
    fun write_clause st (cs, _) =
      put st (space_implode " " (map signed_string_of_int cs) ^ " 0")
    val st = put st ("p cnf " ^ string_of_int n_vars ^ " " ^ string_of_int n_clauses ^ "")
    fun write_clauses st i = if i > n_clauses then st else
      let
        val st = write_clause st (the (Array_Map.sub (clauses, i)))
      in
        write_clauses st (i + 1)
      end
    val st = write_clauses st 1
  in
    st
  end

fun write_dimacs sat dimacs_file =
  let
    val f = TextIO.openOut (Path.implode dimacs_file)
    val _ = dimacs_gen () (fn _ => fn s => TextIO.output (f, s ^ "\n")) sat
    val _ = TextIO.closeOut f
  in
    ()
  end

fun mk_dimacs sat =
  dimacs_gen [] (fn xs => fn s => s :: xs) sat
  |> rev
  |> space_implode "\n"

fun replay_grat ctxt ((n_vars, vars), (n_clauses, clauses), hyp_thm, ctxt') grat_file =
  let
    val is_xz =
      case Path.split_ext grat_file of
        (_, "xz") => true
      | _ => false
    val rup_input =
    {
      ctxt = ctxt',
      clauses = clauses,
      vars = vars,
      n_vars = n_vars,
      tracing = false
    } : Replay_RUP.rup_input
  in
    Replay_RUP.replay_rup_file rup_input (grat_file, is_xz)
    |> Thm.implies_intr (Thm.cprop_of hyp_thm)
    |> Thm.elim_implies hyp_thm
    |> Local_Defs.export ctxt' ctxt
    |> snd
  end

fun derive_false ctxt profiles_file grat_file =
  let
    fun mk_thm () =
      let
        val thy = Proof_Context.theory_of ctxt
        val _ = writeln "Generating SAT problem:"
        val sat as ((n_vars, _), (n_clauses, _), _, _) = mk_sat_problem ctxt profiles_file
        val _ =
          writeln ("Generated SAT problems has " ^ Int.toString n_vars ^ " variables, " ^
            Int.toString n_clauses ^ " clauses")
        val path = Path.basic "papp.cnf"
        val _ =
           Export.export thy (Path.binding (path, \<^here>)) [XML.Text (mk_dimacs sat)]
        val _ = writeln (Export.message thy path)
        val _ = writeln " "

        val _ = writeln "Replaying DRUP proof..."
        val start = Timing.start ()
        val thm = replay_grat ctxt sat grat_file
        val _ = writeln (Timing.message (Timing.result start))
      in
        thm
      end
  in
    Goal.prove_future ctxt [] [] \<^prop>\<open>False\<close>
      (fn {context, ...} => HEADGOAL (resolve_tac context [mk_thm ()]))
  end

end
