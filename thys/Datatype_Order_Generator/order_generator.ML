signature ORDER_GENERATOR = 
sig 
  (* 1. pair of result creates the rhs for the < operator, idx 0 results in < *)
  (* 2. pair of result contains list of arguments for recursor, each indexed by 
        first the constructor number
        second the index number 
  *)
  (*                          dtyp_info            order   idx        *)
  val mk_less_idx : theory -> Datatype_Aux.info -> sort -> (int -> term) * (term * int * int) list;

  (* given an idx, x, and y, it creates x <= y *)
  (*                             dtyp_info            order   idx     x       y   *)
  val mk_less_eq_idx : theory -> Datatype_Aux.info -> sort -> (int -> term -> term -> term);
  
  (* returns the transitivity theorem(s) as a term in combination with the list of free variables
     and a list of each individual transitivity theorem attached with the free variables *)
  val mk_trans_thm_trm : theory -> Datatype_Aux.info -> (term * string list * (term * term list) list);

  (* returns a binary theorem(s) as a term in combination with the list of free variables
     and a list of each individual transitivity theorem attached with the free variables *)
  (*                                                       less                      lesseq                     x       y     property *)
  val mk_binary_thm_trm : theory -> Datatype_Aux.info -> ((term -> term -> term) -> (term -> term -> term) -> term -> term -> term) -> sort
     -> (term * string list * (term * term list) list);

  (* returns the transitivity theorem(s) as a term in combination with the list of free variables
     and a list of each individual transitivity theorem attached with the free variables *)
  val mk_trans_eq_thm_trm : theory -> Datatype_Aux.info -> term * term list;

  (* proves the transitivity theorems (for \<le> and < ) *)
  val mk_transitivity_thms : Proof.context -> Datatype_Aux.info -> thm * thm;

  (* proves a binary theorem *)
  val mk_binary_thm : Proof.context -> Datatype_Aux.info -> 
    (* thm - term generator *)
    ((term -> term -> term) -> (term -> term -> term) -> term -> term -> term) -> 
    (* how many hypothesis does thm have *)
    int -> 
    (* sort constraint *) 
    sort -> 
    (* tactic for solving same constructor case where x = C(params_x) and y = C(params_y) and C is j-th constructor *)
    (* ctxt             ih_hyps   ih_prems   y=C(..)  solve_tac              j      param_x      params_y         c_info                          mk_less *)
    (Proof.context -> thm list -> thm list -> thm -> (thm list -> tactic) -> int -> term list -> term list -> string * Datatype_Aux.dtyp list -> (Datatype.dtyp -> term -> term -> term) -> tactic) ->
    thm;

  val mk_less_disj : (Datatype_Aux.dtyp -> term -> term -> term) -> term list -> term list -> Datatype_Aux.dtyp list -> term;

  (* proves the theorem (x < y) = (x \<le> y \<and> \<not> y \<le> x) *)
  val mk_less_le_not_le_thm : Proof.context -> Datatype_Aux.info -> thm

  (* proves the theorem (x \<le> x) *)
  val mk_le_refl_thm : Proof.context -> Datatype_Aux.info -> thm

  (* proves the theorem (x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y) *)
  (* takes as input the transitivity thm for < and the less_le_not_le thm *)
  val mk_antisym_thm : Proof.context -> Datatype_Aux.info -> thm -> thm -> thm

  (* proves the theorem (x \<le> y \<or> y \<le> x) *)
  val mk_linear_thm : Proof.context -> Datatype_Aux.info -> thm

  (* proves all four theorems which are required for orders: trans, refl, antisym, less_le_not_le *)
  val mk_order_thms : Proof.context -> Datatype_Aux.info -> thm list

  (* instantiates a thm for given terms of given sort *)
  val instantiate' : theory -> sort -> term list -> thm -> thm

  (* creates and registers linear-order for datatype *)
  val setup : string -> theory -> theory

end

structure Order_Generator : ORDER_GENERATOR =
struct
open Datatype_Aux; open Datatype;

(* [a,b,c,...,z] -> [(0,a),(1,b),...,(25,z)] *)
fun number_list xs = List.tabulate (length xs,I) ~~ xs 

(* delivers a typ substitution which constrains all free type variables in datatype by sort *)
fun typ_subst_for_sort thy info sort =
  let val spec = #descr info |> hd |> (fn (_,(dty_name,_,_)) => dty_name)
        |> the_spec thy
      val typ_subst = Term.typ_subst_atomic (spec |> fst |> map (fn (n,s) => (TFree (n,s), TFree (n,sort)))) 
  in typ_subst end

val less_name = @{term "op <"} |> Term.dest_Const |> fst

(* construct free variable x_i *)
fun mk_free_tysubst_i typ_subst x i ty = Free (x ^ string_of_int i, ty |> typ_subst)

fun mk_less_idx thy info sort =
  let val typ_subst = typ_subst_for_sort thy info sort 
      val descr = #descr info
      fun typ_of dty = typ_of_dtyp descr dty |> typ_subst
      val rec_names = #rec_names info
      val mk_free_i = mk_free_tysubst_i typ_subst
      fun dtrecs [] j = (j,[]) 
        | dtrecs (DtTFree _ :: dtys) j = dtrecs dtys j
        | dtrecs (DtRec i :: dtys) j = 
           let val (j',ijs) = dtrecs dtys (j+1)
           in (j',(i,j) :: ijs) end
        | dtrecs (DtType (_,dtys1) :: dtys2) j = 
           let val (j',ijs) = dtrecs dtys1 j
               val (j'',ijs') = dtrecs dtys2 j'
           in (j'',ijs @ ijs') end
      fun rec_idx i dtys = dtrecs (take i dtys) 0 |> fst
      fun mk_rhss (idx,(ty_name,_,cons)) = 
        let val ty = typ_of (DtRec idx) 
            val linfo = the_info thy ty_name
            val case_name = #case_name linfo
            val ncons = number_list cons
            fun mk_rhs (i,(_,dtysi)) = 
            let val lvars = number_list dtysi
                         |> map (fn (i,dty) => mk_free_i "x_" i (typ_of dty))
                fun res_var (i,oc) = mk_free_i "res_" oc (typ_of (DtRec i) --> @{typ bool});
                val res_vars = dtrecs dtysi 0
                         |> snd 
                         |> map res_var
                fun mk_case (j,(_,dtysj)) = 
                let val rvars = number_list dtysj
                              |> map (fn (i,dty) => mk_free_i "y_" i (typ_of dty))
                    val x = nth lvars
                    val y = nth rvars                    
                    fun combine_dts [] = @{term False}
                      | combine_dts ((_,c) :: []) = c
                      | combine_dts ((i,c) :: ics) = HOLogic.mk_disj (c, HOLogic.mk_conj (HOLogic.mk_eq (x i, y i), combine_dts ics))
                    fun less_of_dty (i,DtRec j) = res_var (j,rec_idx i dtysj) $ y i
                      | less_of_dty (i,_) = let
                           val xi = x i
                           val ty = Term.type_of xi
                           val less = Const (less_name, ty --> ty --> @{typ bool})
                        in less $ xi $ y i end
                    val rhs = if i < j then @{term True} 
                         else if i > j then @{term False}
                         else dtysi
                            |> number_list
                            |> map less_of_dty
                            |> number_list
                            |> combine_dts
                    val lam_rhs = fold lambda (rev rvars) rhs
                in lam_rhs end
                val cases = map mk_case ncons
                val case_ty = (map type_of cases @ [ty]) ---> @{typ bool}
                val rhs_case = list_comb (Const (case_name, case_ty), cases)
                val rhs = fold lambda (rev (lvars @ res_vars)) rhs_case
            in rhs end
            val rec_args = map (fn (i,c) => (mk_rhs (i,c),i,idx)) ncons 
         in rec_args end
      val nrec_args = List.concat (map mk_rhss descr)
      val rec_args = map #1 nrec_args
      fun mk_rec i = 
      let val ty = typ_of (DtRec i)
          val rec_ty = map type_of rec_args @ [ty,ty] ---> @{typ bool}
          val rec_name = nth rec_names i
          val rhs = list_comb (Const (rec_name, rec_ty), rec_args)
       in rhs end
  in (mk_rec,nrec_args) end

fun mk_less_eq_idx thy info sort idx x y = 
  mk_less_idx thy info sort 
  |> fst
  |> (fn less => HOLogic.mk_disj (less idx $ x $ y, HOLogic.mk_eq (x,y)))

fun mk_xs_ys_zs thy info sort =   
  let val descr = #descr info
      val typ_subst = typ_subst_for_sort thy info sort
      fun typ_of dty = typ_of_dtyp descr dty |> typ_subst
      val mk_free_i = mk_free_tysubst_i typ_subst
      val idxs = map fst descr
      fun mk_free x i = mk_free_i x i (typ_of (DtRec i))
      fun list x = map (mk_free x) idxs 
   in 
      (list "x", list "y", list "z")      
   end

fun mk_trans_thm_trm thy info =
  let val descr = #descr info
      val sort = @{sort "order"}
      val (xs,ys,zs) = mk_xs_ys_zs thy info sort
      val mk_rec = mk_less_idx thy info sort |> fst
      val idxs = map fst descr
      val recs_list = map mk_rec idxs
      val recs = nth recs_list 
      fun mk_trans_props i =
      let val x = nth xs i
          val y = nth ys i
          val z = nth zs i
          val less_term = recs i
          fun less x y = less_term $ x $ y
          val xy = less x y |> HOLogic.mk_Trueprop
          val yz = less y z |> HOLogic.mk_Trueprop
          val xz = less x z |> HOLogic.mk_Trueprop
          val trm = Logic.list_implies ([xy,yz], xz)
          val vars = [x,y,z]
        in (trm,vars) end
      val trans_props = map mk_trans_props idxs
      val trans_trm = trans_props
             |> map fst
             |> Logic.mk_conjunction_list
      val trans_vars = List.concat (map snd trans_props)
   in (trans_trm,map (fst o dest_Free) trans_vars,trans_props) end

fun mk_binary_thm_trm thy info p_gen sort =
  let val descr = #descr info
      val (xs,ys,_) = mk_xs_ys_zs thy info sort
      val mk_rec = mk_less_idx thy info sort |> fst
      val idxs = map fst descr
      val recs_list = map mk_rec idxs
      val recs = nth recs_list 
      fun mk_p_props i =
      let val x = nth xs i
          val y = nth ys i
          val less_term = recs i
          fun less x y = less_term $ x $ y
          fun lesseq x y = HOLogic.mk_disj (less x y, HOLogic.mk_eq (x,y))
          val trm = p_gen less lesseq x y
          val vars = [x,y]
        in (trm,vars) end
      val p_props = map mk_p_props idxs
      val p_trm = p_props
             |> map fst
             |> Logic.mk_conjunction_list
      val p_vars = List.concat (map snd p_props)
   in (p_trm,map (fst o dest_Free) p_vars,p_props) end

fun mk_trans_eq_thm_trm thy info =
  let val sort = @{sort "order"}
      val (xs,ys,zs) = mk_xs_ys_zs thy info sort
      val less_eq = mk_less_eq_idx thy info sort 0
      val x = hd xs
      val y = hd ys
      val z = hd zs
      val xy = less_eq x y |> HOLogic.mk_Trueprop
      val yz = less_eq y z |> HOLogic.mk_Trueprop
      val xz = less_eq x z |> HOLogic.mk_Trueprop
      val trm = Logic.list_implies ([xy,yz], xz)
  in 
    (trm,[x,y,z])
  end

fun strip_cases ctac = ctac #> Seq.map snd

fun first_conj thm = if (thm |> Thm.prop_of |> head_of |> dest_Const |> fst) = "Pure.conjunction" then
  first_conj (@{thm conjunctionD1} OF [thm]) else thm

fun mk_case_tac (ctxt : Proof.context)
  (insts : term option list list) 
  (thm : thm) 
  (sub_case_tac : Proof.context * int * thm list * (string * cterm) list -> tactic) = 
    (DETERM o strip_cases o Induct.cases_tac ctxt false insts (SOME thm) []
     THEN_ALL_NEW (fn i => Subgoal.SUBPROOF (fn {context = ctxt, prems = hyps, params = params, ...} => sub_case_tac (ctxt, i-1, hyps, params)) ctxt i)) 
    1

fun mk_solve_with_tac (thms : thm list) 
  (solver_tac : tactic)
  = SOLVE (Method.insert_tac thms 1 THEN solver_tac)

fun mk_less_disj mk_less px py dtys = let
  fun build_disj [] _ _ = @{term False}
    | build_disj (px :: xs) (py :: ys) (dty :: dtys) = 
         HOLogic.mk_disj (mk_less dty px py, HOLogic.mk_conj (HOLogic.mk_eq (px,py),build_disj xs ys dtys))
in 
  HOLogic.mk_Trueprop (build_disj px py dtys)
end;

fun instantiate' thy sort vars thm = 
  let val tvars = Thm.prop_of thm |> Term.add_tvars |> (fn x => x []) |> rev
      val inst_tvars = map (fn (n,s) => TFree (fst n,sort) |> ctyp_of thy |> SOME) tvars
      val cvars = map (cterm_of thy #> SOME) vars
  in 
    Drule.instantiate' inst_tvars cvars thm
  end


fun mk_transitivity_thms ctxt info = 
  let val thy = Proof_Context.theory_of ctxt
      (* first prove transitivity of < *)
      val (trans_trm,trans_vars_strings,trans_props) = mk_trans_thm_trm thy info
      val sort = @{sort "order"}
      val (mk_rec,nrec_args) = mk_less_idx thy info sort
      val typ_subst = typ_subst_for_sort thy info sort
      val descr = #descr info
      fun typ_of dty = typ_of_dtyp descr dty |> typ_subst
      fun mk_less_term (DtRec i) = mk_rec i
        | mk_less_term dty =
          let val ty = typ_of dty
          in Const (less_name, ty --> ty --> @{typ bool}) end;
      fun mk_less dty x y = mk_less_term dty $ x $ y;
      val ind_vars = (map (snd #> hd #> (fn x => [SOME (NONE, (x,false))])) trans_props) (* TODO: why false *)
      val arbi_vars = (map (snd #> tl #> map dest_Free) trans_props)
      val ind_thms = #inducts info
      val ind_tac = DETERM o strip_cases o Induct.induct_tac ctxt false ind_vars arbi_vars
         []
         (SOME ind_thms)
         []
      val solve_with_tac = (fn thms => mk_solve_with_tac thms (asm_full_simp_tac (simpset_of ctxt) 1))
      fun ind_case_tac i = Subgoal.SUBPROOF (fn {context = ctxt, prems = ihyps, params = iparams, ...} => 
      let val (rhyps,yz) = split_last ihyps
          val (hyps,xy) = split_last rhyps
          val (rparams,z) = split_last (map (snd #> term_of) iparams) 
          val (params_x,y) = split_last rparams
          val (j,idx) = nth nrec_args (i-1) |> (fn (_,j,idx) => (j,idx))
          val linfo = nth descr idx |> (fn (_,(ty_name,_,_)) => ty_name) |> the_info thy
          fun case_tac ctxt y_z = mk_case_tac ctxt [[SOME y_z]] (#exhaust linfo)
          fun sub_case_tac (ctxt,k,prems,iparams_y) = 
          let val case_hyp_y = hd prems 
              fun sub_sub_case_tac (ctxt,l,prems,iparams_z) = 
              let val case_hyp_z = hd prems
                  val comp_eq = [case_hyp_z, case_hyp_y, xy, yz]
              in (if not (j = l andalso l = k) then K (solve_with_tac comp_eq) else
                 let val params_y = map (snd #> term_of) iparams_y
                     val params_z = map (snd #> term_of) iparams_z
                     val c_info = nth descr idx |> snd |> (fn (_,_,info) => nth info j)
                     val pdtys = snd c_info
                     val build_disj = mk_less_disj mk_less
                     val xy' = build_disj params_x params_y pdtys 
                     val yz' = build_disj params_y params_z pdtys 
                     fun disj_thm t = Goal.prove ctxt [] [] t (K (solve_with_tac comp_eq))
                     val xy_disj = disj_thm xy'
                     val yz_disj = disj_thm yz'
                     fun solve_tac xy yz [] _ _ _ eqs ihyps = K (solve_with_tac [xy])
                       | solve_tac xy yz (px :: pxs) (py :: pys) (pz :: pzs) (dty :: dtys) eqs ihyps =
                         let fun case_tac_disj disj tac = 
                               mk_case_tac ctxt [] (@{thm disjE} OF [disj]) (fn (ctxt,ii,hyps,_) => tac ii ctxt (List.last hyps))
                             val yz_case_tac = case_tac_disj yz
                             val rec_type = (fn DtRec _ => true | _ => false) dty
                             fun xy_tac ii ctxt hyp_xy = 
                             if ii = 1 (* right branch, px = py and pxs < pys *) 
                             then let val eq_term = HOLogic.mk_eq (px,py) |> HOLogic.mk_Trueprop
                                      val eq_xy_thm = Goal.prove ctxt [] [] eq_term (K (solve_with_tac [hyp_xy]))
                                      val xy'_thm = Goal.prove ctxt [] [] (build_disj pxs pys dtys) (K (solve_with_tac [hyp_xy]))
                                      fun yz_tac jj ctxt hyp_yz = 
                                      if jj = 1 (* right branch, py = pz and pys < pzs *)
                                        (* = and = *)
                                      then let val eq_term = HOLogic.mk_eq (px,pz) |> HOLogic.mk_Trueprop
                                               val eq_thm  = Goal.prove ctxt [] [] eq_term (K (solve_with_tac [eq_xy_thm,hyp_yz]))
                                               val yz'_thm = Goal.prove ctxt [] [] (build_disj pys pzs dtys) (K (solve_with_tac [hyp_yz]))
                                               val drop_hyps = if rec_type then tl else I
                                           in
                                               solve_tac xy'_thm yz'_thm pxs pys pzs dtys (eq_thm :: eqs) (drop_hyps ihyps) 1
                                           end
                                      else (* left branch, py < pz *) let 
                                        (* = and < *)
                                               val xz_term = mk_less dty px pz |> HOLogic.mk_Trueprop
                                               val xz_thm  = Goal.prove ctxt [] [] xz_term (K (solve_with_tac [hyp_xy,hyp_yz]))
                                            in
                                              solve_with_tac (xz_thm :: case_hyp_z :: eqs)
                                            end
                                   in
                                     yz_case_tac yz_tac
                                   end
                             else (* left branch, px < py *) let
                                       val xz_term = mk_less dty px pz |> HOLogic.mk_Trueprop
                                       val xz_goal = Goal.prove ctxt [] [] xz_term
                                       fun yz_tac jj _ hyp_yz = 
                                       if jj = 1 (* right branch, py = pz *)
                                         (* < and = *)
                                       then let 
                                                val xz_thm  = xz_goal (K (solve_with_tac [hyp_xy,hyp_yz]))
                                            in
                                              solve_with_tac (xz_thm :: case_hyp_z :: eqs)
                                            end
                                       else (* left branch, py < pz *) let 
                                          (* < and < *)
                                                 val trans_thm = if rec_type then hd ihyps else @{thm less_trans}
                                                 val tac = rtac (trans_thm OF [hyp_xy,hyp_yz]) 1
                                                 val xz_thm  = xz_goal (K tac)
                                            in 
                                               solve_with_tac (xz_thm :: case_hyp_z :: eqs)
                                            end
                                   in
                                     yz_case_tac yz_tac
                                   end
                             ;
                             val xy_case_tac = case_tac_disj xy xy_tac
                         in 
                           K (print_tac ("another case: ") THEN xy_case_tac)
                         end
                 in 
                   K (print_tac "recursive case: ") 
                   THEN' solve_tac xy_disj yz_disj params_x params_y params_z pdtys [] hyps 
                 end) 
             1 end              
          in print_tac ("consider constructor " ^ string_of_int k) THEN 
             (if k >= j then case_tac ctxt z sub_sub_case_tac else 
                solve_with_tac [case_hyp_y,xy]) 
          end 
      in print_tac ("start induct " ^ string_of_int i) THEN case_tac ctxt y sub_case_tac end) ctxt i
      val tac = print_tac "start proving transitivity" THEN (ind_tac THEN_ALL_NEW ind_case_tac) 1
      fun tac_to_thm tac = Goal.prove ctxt trans_vars_strings [] trans_trm (K tac)
      (* in the end only return main transitivity thm for major datatype and < *)
      val trans_thm = first_conj (tac_to_thm tac)
      val (trans_eq_trm,vars) = mk_trans_eq_thm_trm thy info
      val inst_trans = instantiate' thy sort vars trans_thm 
      val trans_eq_vars_string = map (dest_Free #> fst) vars
      fun tac_to_eq_thm tac = Goal.prove ctxt trans_eq_vars_string [] trans_eq_trm (K tac)
      val eq_tac = mk_solve_with_tac [inst_trans] (blast_tac ctxt 1)
      val trans_eq_thm = tac_to_eq_thm eq_tac
  in (trans_thm,trans_eq_thm) end 

fun mk_binary_thm ctxt info prop_gen numprems sort same_constructor_tac = 
  let val thy = Proof_Context.theory_of ctxt
      val (prop_trm,prop_vars_strings,prop_props) = mk_binary_thm_trm thy info prop_gen sort
      val (mk_rec,nrec_args) = mk_less_idx thy info sort
      val typ_subst = typ_subst_for_sort thy info sort
      val descr = #descr info
      fun typ_of dty = typ_of_dtyp descr dty |> typ_subst
      fun mk_less_term (DtRec i) = mk_rec i
        | mk_less_term dty =
          let val ty = typ_of dty
          in Const (less_name, ty --> ty --> @{typ bool}) end;
      fun mk_less dty x y = mk_less_term dty $ x $ y;
      val ind_vars = (map (snd #> hd #> (fn x => [SOME (NONE, (x,false))])) prop_props) (* TODO: why false *)
      val arbi_vars = (map (snd #> tl #> map dest_Free) prop_props)
      val ind_thms = #inducts info
      val ind_tac = DETERM o strip_cases o Induct.induct_tac ctxt false ind_vars arbi_vars
         []
         (SOME ind_thms)
         []
      val solve_with_tac = (fn thms => mk_solve_with_tac thms (force_tac ctxt 1))
      fun ind_case_tac i = Subgoal.SUBPROOF (fn {context = ctxt, prems = ihyps, params = iparams, ...} => 
      let val numhyps = length ihyps - numprems 
          val hyps = take numhyps ihyps
          val ihprems = drop numhyps ihyps
          val (params_x,y) = split_last (map (snd #> term_of) iparams) 
          val (j,idx) = nth nrec_args (i-1) |> (fn (_,j,idx) => (j,idx))
          val linfo = nth descr idx |> (fn (_,(ty_name,_,_)) => ty_name) |> the_info thy
          fun case_tac ctxt = mk_case_tac ctxt [[SOME y]] (#exhaust linfo)
          fun sub_case_tac (ctxt,k,prems,iparams_y) = 
          let val case_hyp_y = hd prems 
          in (if not (j = k) then print_tac ("different constructors ") THEN solve_with_tac (case_hyp_y :: ihprems) (* different constructor *) else
               let val params_y = map (snd #> term_of) iparams_y
                   val c_info = nth descr idx |> snd |> (fn (_,_,info) => nth info j)
               in 
                  print_tac ("consider constructor " ^ string_of_int k) THEN
                  same_constructor_tac ctxt hyps ihprems case_hyp_y solve_with_tac j params_x params_y c_info mk_less
               end)
          end 
      in print_tac ("start induct " ^ string_of_int i) THEN case_tac ctxt sub_case_tac end) ctxt i
      val tac = print_tac "start proving binary theorem" THEN (ind_tac THEN_ALL_NEW ind_case_tac) 1
      fun tac_to_thm tac = Goal.prove ctxt prop_vars_strings [] prop_trm (K tac)
      (* in the end only return main binary thm *)
      val prop_thm = first_conj (tac_to_thm tac)
  in prop_thm end 

fun mk_less_le_not_le_thm ctxt info = let
  val sort = @{sort "order"}
  (* main property: x < y \<Longrightarrow> \<not> y \<le> x *)
  fun prop_gen less lesseq x y = Logic.mk_implies (less x y |> HOLogic.mk_Trueprop, lesseq y x |> HOLogic.mk_not |> HOLogic.mk_Trueprop)
  fun main_tac ctxt ih_hyps ih_prems y_prem solve_with_tac j params_x params_y c_info mk_less = 
  let val pdtys = snd c_info
      val comp_eq = y_prem :: ih_prems
      val build_disj = mk_less_disj mk_less
      val xy' = build_disj params_x params_y pdtys 
      val xy_disj = Goal.prove ctxt [] [] xy' (K (solve_with_tac comp_eq))
      fun solve_tac xy [] _ _ eqs ihyps = solve_with_tac [xy]
        | solve_tac xy (px :: pxs) (py :: pys) (dty :: dtys) eqs ihyps =
           let val xs_ys = build_disj pxs pys dtys
               val x_eq_y = HOLogic.mk_eq (px,py)
               val x_less_y = mk_less dty px py
               val disj2 = HOLogic.mk_disj (x_less_y, HOLogic.mk_conj (HOLogic.mk_not x_less_y, HOLogic.mk_conj( x_eq_y, HOLogic.dest_Trueprop xs_ys)))
                         |> HOLogic.mk_Trueprop
               val disj2_thm = Goal.prove ctxt [] [] disj2 (K (Method.insert_tac [xy] 1 THEN blast_tac ctxt 1))
               fun case_tac_disj disj tac = 
                 mk_case_tac ctxt [] (@{thm disjE} OF [disj]) (fn (ctxt,ii,hyps,_) => tac ii ctxt (List.last hyps))
               val rec_type = (fn DtRec _ => true | _ => false) dty
               fun xy_tac ii ctxt hyp_xy = 
               if ii = 1 then (* right branch, px = py and \<not> px < py and pxs < pys *) let
                      val eq_term = x_eq_y |> HOLogic.mk_Trueprop
                      val eq_xy_thm = Goal.prove ctxt [] [] eq_term (K (solve_with_tac [hyp_xy]))
                      val xy'_thm = Goal.prove ctxt [] [] xs_ys (K (solve_with_tac [hyp_xy]))
                      val yx_thm = Goal.prove ctxt [] [] (mk_less dty py px |> HOLogic.mk_not |> HOLogic.mk_Trueprop)
                                   (K (solve_with_tac [hyp_xy]))
                      val ihyps' = if rec_type then tl ihyps else ihyps
                      val solve_rec = solve_tac xy'_thm pxs pys dtys (eq_xy_thm :: yx_thm :: eqs) ihyps'
                    in 
                      solve_rec
                    end
               else (* left branch, px < py *) let
                      (* hence \<not> py \<le> px (yx_thm) *)
                      val yx = HOLogic.mk_disj (mk_less dty py px, HOLogic.mk_eq (py,px)) |> HOLogic.mk_not |> HOLogic.mk_Trueprop
                      val tac = if rec_type then solve_with_tac [hd ihyps OF [hyp_xy]] else solve_with_tac [hyp_xy]
                      val yx_thm = Goal.prove ctxt [] [] yx (K tac)
                    in                                        
                      solve_with_tac (yx_thm :: y_prem :: eqs)
                    end
               ;
           in 
             case_tac_disj disj2_thm xy_tac
           end
  in 
    (solve_tac xy_disj params_x params_y pdtys [] ih_hyps : tactic)
  end
  val main_thm = mk_binary_thm ctxt info prop_gen 1 sort main_tac
  val thy = Proof_Context.theory_of ctxt
  val (thm_trm,vars) = mk_binary_thm_trm thy info (fn less => fn lesseq => fn x => fn y => 
              HOLogic.mk_eq (less x y,HOLogic.mk_conj (lesseq x y, lesseq y x |> HOLogic.mk_not)) |> HOLogic.mk_Trueprop) sort
              |> #3 |> hd
  val inst_thm = instantiate' thy sort vars main_thm
  val vars_strings = map (dest_Free #> fst) vars
  val thm = Goal.prove ctxt vars_strings [] thm_trm (K (Method.insert_tac [inst_thm] 1 THEN blast_tac ctxt 1))
in 
  thm
end

fun mk_le_refl_thm ctxt info = let
  val sort = @{sort "order"}
  (* x \<le> x *)
  val thy = Proof_Context.theory_of ctxt
  val (thm_trm,vars) = mk_binary_thm_trm thy info (fn less => fn lesseq => fn x => fn y => 
              lesseq x x |> HOLogic.mk_Trueprop) sort
              |> #3 |> hd
  val vars_strings = map (dest_Free #> fst) vars
  in 
    Goal.prove ctxt vars_strings [] thm_trm (K (blast_tac ctxt 1))
end

fun mk_antisym_thm ctxt info trans_thm less_thm = let
  val sort = @{sort "order"}
  (* x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y *)
  val thy = Proof_Context.theory_of ctxt
  val (thm_trm,vars) = mk_binary_thm_trm thy info (fn less => fn lesseq => fn x => fn y => 
              Logic.list_implies ([lesseq x y |> HOLogic.mk_Trueprop, lesseq y x |> HOLogic.mk_Trueprop],
                         HOLogic.mk_eq (x,y) |> HOLogic.mk_Trueprop)) sort
              |> #3 |> hd
  val vars_strings = map (dest_Free #> fst) vars
  val tvars = vars @ [hd vars]
  val lvars = [hd vars,hd vars]
  fun inst_thm vars thm = instantiate' thy sort vars thm
  val inst_trans = inst_thm tvars trans_thm
  val inst_less = inst_thm lvars less_thm
  val res = Goal.prove ctxt vars_strings [] thm_trm (K (Method.insert_tac [inst_trans,inst_less] 1 THEN blast_tac ctxt 1))
  in 
    res
end

fun mk_order_thms ctxt info = let
  val (trans,trans_eq) = mk_transitivity_thms ctxt info
  val less = mk_less_le_not_le_thm ctxt info 
  val refl = mk_le_refl_thm ctxt info 
  val antisym = mk_antisym_thm ctxt info trans less
  val res = [trans_eq,less,refl,antisym]
  in res
end 

fun mk_linear_thm ctxt info = let
  val sort = @{sort "linorder"}
  (* main property: x = y \<or> x < y \<or> y < x *)
  fun prop_gen less lesseq x y = HOLogic.mk_disj (HOLogic.mk_eq (x,y),HOLogic.mk_disj(less x y, less y x)) |> HOLogic.mk_Trueprop
  fun main_tac ctxt ih_hyps ih_prems y_prem solve_with_tac j params_x params_y c_info mk_less = 
  let val pdtys = snd c_info
      fun solve_tac [] _ _ eqs ihyps = solve_with_tac eqs
        | solve_tac (px :: pxs) (py :: pys) (dty :: dtys) eqs ihyps =
           let val less = mk_less dty
               val x_eq_y = HOLogic.mk_eq (px,py)
               val disj_trm = HOLogic.mk_disj (x_eq_y,HOLogic.mk_disj(less px py, less py px)) |> HOLogic.mk_Trueprop
               val rec_type = (fn DtRec _ => true | _ => false) dty
               val disj_thm' = if rec_type then hd ihyps else @{thm linear_cases}
               val disj_tac = rtac disj_thm' 1 
               val disj_thm = Goal.prove ctxt [] [] disj_trm (K (disj_tac))
               fun case_tac_disj disj tac = 
                 mk_case_tac ctxt [] (@{thm disjE} OF [disj]) (fn (ctxt,ii,hyps,_) => tac ii ctxt (List.last hyps))
               fun eq_less_less_tac ii ctxt eq_less = 
               if ii = 0 then (* left branch, px = py *) let
                      val ihyps' = if rec_type then tl ihyps else ihyps
                      val solve_rec = solve_tac pxs pys dtys (eq_less :: eqs) ihyps'
                    in 
                      solve_rec
                    end
               else (* right branch, px < py \<or> py < px *) let
                      fun less_tac _ _ less = solve_with_tac (less :: eqs)
                    in                                        
                      case_tac_disj eq_less less_tac
                    end; 
           in 
             case_tac_disj disj_thm eq_less_less_tac
           end
  in 
    (solve_tac params_x params_y pdtys [y_prem] ih_hyps : tactic)
  end
  val main_thm = mk_binary_thm ctxt info prop_gen 0 sort main_tac
  val thy = Proof_Context.theory_of ctxt
  (* x \<le> y \<or> y \<le> x *)
  val (thm_trm,vars) = mk_binary_thm_trm thy info (fn less => fn lesseq => fn x => fn y => 
              HOLogic.mk_disj (lesseq x y,lesseq y x) |> HOLogic.mk_Trueprop) sort
              |> #3 |> hd
  val inst_thm = instantiate' thy sort vars main_thm
  val vars_strings = map (dest_Free #> fst) vars
  val thm = Goal.prove ctxt vars_strings [] thm_trm (K (Method.insert_tac [inst_thm] 1 THEN blast_tac ctxt 1))
in 
  thm
end

fun setup dtyp_name thy = let
  val tyco = dtyp_name

  (* first register in class ord *)
  val base_name = Long_Name.base_name tyco
  val _ = Output.writeln ("creating orders for datatype " ^ base_name)
  val sort = @{sort ord}
  val info = Datatype.the_info thy tyco
  val vs_of_sort = let val i = Datatype.the_spec thy tyco |> #1 in 
     fn sort => map (fn (n,s) => (n, sort)) i end
  val vs = vs_of_sort sort
  val less_rhs = mk_less_idx thy info sort |> fst |> (fn x => x 0)
  val ty = Term.fastype_of less_rhs |> Term.dest_Type |> snd |> hd

  (* code copied from HOL/SPARK/TOOLS *)
  fun mk_binrel_def T c rhs = Logic.mk_equals
      (Const (c, T --> T --> HOLogic.boolT), rhs)
  fun define_overloaded (def_name, eq) lthy =
    let
      val ((c, _), rhs) = eq |> Syntax.check_term lthy |>
        Logic.dest_equals |>> dest_Free;
      val ((_, (_, thm)), lthy') = Local_Theory.define
        ((Binding.name c, NoSyn), ((Binding.name def_name, @{attributes [code]}), rhs)) lthy
      val ctxt_thy = Proof_Context.init_global (Proof_Context.theory_of lthy');
      val thm' = singleton (Proof_Context.export lthy' ctxt_thy) thm
    in (thm', lthy') end;

  fun get_global_thms ctxt_to_thms lthy = let
    val ctxt = Proof_Context.init_global (Proof_Context.theory_of lthy)
    val thms = Proof_Context.export lthy ctxt (ctxt_to_thms ctxt)
  in thms end

  val less_def = mk_binrel_def ty @{const_name less} less_rhs
  val x = Free ("x",ty)
  val y = Free ("y",ty)
  val less_eq_rhs = lambda x (lambda y (HOLogic.mk_disj (less_rhs $ x $ y, HOLogic.mk_eq (x,y))))
  val less_eq_def = mk_binrel_def ty @{const_name less_eq} less_eq_rhs
  val ((less_thm,less_eq_thm),lthy) = Class.instantiation ([tyco],vs,sort) thy
      |> define_overloaded ("less_" ^ base_name ^ "_def", less_def)
      ||>> define_overloaded ("less_eq_" ^ base_name ^ "_def", less_eq_def)
  val less_thms = [less_thm, less_eq_thm]
   
  val thy' = Class.prove_instantiation_exit (K (Class.intro_classes_tac [])) lthy
  val _ = Output.writeln ("registered " ^ base_name ^ " in class ord")

  (* next register in class order *)
  val sort = @{sort order}
  val vs = vs_of_sort sort
  val lthy = Class.instantiation ([tyco],vs,sort) thy'

  fun order_tac ctxt = 
    let val [trans_eq,less,refl,antisym] = get_global_thms (fn ctxt => mk_order_thms ctxt info) lthy
    in (print_tac "enter order" THEN
       unfold_tac less_thms (simpset_of ctxt) THEN
       print_tac "after unfolding" THEN
       rtac less 1 THEN
       print_tac "after less" THEN
       rtac refl 1 THEN
       print_tac "after refl" THEN
       rtac trans_eq 1 THEN atac 1 THEN atac 1 THEN
       print_tac "after trans" THEN
       rtac antisym 1 THEN atac 1 THEN atac 1
       )
    end
  val thy'' = Class.prove_instantiation_exit (fn ctxt => (Class.intro_classes_tac [] THEN order_tac ctxt)) lthy
  val _ = Output.writeln ("registered " ^ base_name ^ " in class order")

  (* next register in class linorder *)
  val sort = @{sort linorder}
  val vs = vs_of_sort sort
  val lthy = Class.instantiation ([tyco],vs,sort) thy''
  fun order_tac ctxt = 
    let val [linear] = get_global_thms (fn ctxt => [mk_linear_thm ctxt info]) lthy
    in (unfold_tac less_thms (simpset_of ctxt) THEN
       rtac linear 1 
       )
    end
  val thy''' = Class.prove_instantiation_exit (fn ctxt => (Class.intro_classes_tac [] THEN order_tac ctxt)) lthy
  val _ = Output.writeln ("registered " ^ base_name ^ " in class linorder")

in thy''' end

val _ = Outer_Syntax.command @{command_spec "derive_order"} "derives a linear order for a datatype"
        (Parse.string >> (fn dtyp_name => Toplevel.theory (fn thy =>
          let val full_name = Syntax.parse_typ (Proof_Context.init_global thy) dtyp_name |> dest_Type |> fst
            in setup full_name thy end))) 

end
