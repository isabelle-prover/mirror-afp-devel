(*  Title:      nominal_thmdecls.ML
    Author:     Christian Urban

  Infrastructure for the lemma collection "eqvts".

  Provides the attributes [eqvt] and [eqvt_raw], and the theorem
  lists eqvts and eqvts_raw. The first attribute will store the 
  theorem in the eqvts list and also in the eqvts_raw list. For 
  the latter the theorem is expected to be of the form

    p o (c x1 x2 ...) = c (p o x1) (p o x2) ...    (1)

  or

    c x1 x2 ... ==> c (p o x1) (p o x2) ...        (2)

  and it is stored in the form

    p o c == c

  The [eqvt_raw] attribute just adds the theorem to eqvts_raw.

  TODO: In case of the form in (2) one should also
        add the equational form to eqvts
*)

signature NOMINAL_THMDECLS =
sig
  val eqvt_add: attribute
  val eqvt_del: attribute
  val eqvt_raw_add: attribute
  val eqvt_raw_del: attribute
  val setup: theory -> theory
  val get_eqvts_thms: Proof.context -> thm list
  val get_eqvts_raw_thms: Proof.context -> thm list
  val eqvt_transform: Proof.context -> thm -> thm
  val is_eqvt: Proof.context -> term -> bool
end;

structure Nominal_ThmDecls: NOMINAL_THMDECLS =
struct

structure EqvtData = Generic_Data
( type T = thm Item_Net.T;
  val empty = Thm.full_rules;
  val extend = I;
  val merge = Item_Net.merge);

structure EqvtRawData = Generic_Data
( type T = thm Termtab.table;
  val empty = Termtab.empty;
  val extend = I;
  val merge = Termtab.merge (K true));

val eqvts = Item_Net.content o EqvtData.get;
val eqvts_raw = map snd o Termtab.dest o EqvtRawData.get;

val get_eqvts_thms = eqvts o  Context.Proof;
val get_eqvts_raw_thms = eqvts_raw o Context.Proof;

fun checked_update key net =
  (if Item_Net.member net key then 
     warning "Theorem already declared as equivariant."
   else (); 
   Item_Net.update key net)

val add_thm = EqvtData.map o checked_update;
val del_thm = EqvtData.map o Item_Net.remove;

fun add_raw_thm thm = 
  case prop_of thm of
    Const ("==", _) $ _ $ (c as Const _) => EqvtRawData.map (Termtab.update (c, thm)) 
  | _ => raise THM ("Theorem must be a meta-equality where the right-hand side is a constant.", 0, [thm]) 

fun del_raw_thm thm = 
  case prop_of thm of
    Const ("==", _) $ _ $ (c as Const _) => EqvtRawData.map (Termtab.delete c)
  | _ => raise THM ("Theorem must be a meta-equality where the right-hand side is a constant.", 0, [thm]) 

fun is_eqvt ctxt trm =
  case trm of 
    (c as Const _) => Termtab.defined (EqvtRawData.get (Context.Proof ctxt)) c
  | _ => false (* raise TERM ("Term must be a constant.", [trm]) *)



(** transformation of eqvt lemmas **)

fun get_perms trm =
  case trm of 
     Const (@{const_name permute}, _) $ _ $ (Bound _) => 
       raise TERM ("get_perms called on bound", [trm])
   | Const (@{const_name permute}, _) $ p $ _ => [p]
   | t $ u => get_perms t @ get_perms u
   | Abs (_, _, t) => get_perms t 
   | _ => []

fun add_perm p trm =
  let
    fun aux trm = 
      case trm of 
        Bound _ => trm
      | Const _ => trm
      | t $ u => aux t $ aux u
      | Abs (x, ty, t) => Abs (x, ty, aux t)
      | _ => mk_perm p trm
  in
    strip_comb trm
    ||> map aux
    |> list_comb
  end  


(* tests whether there is a disagreement between the permutations, 
   and that there is at least one permutation *)
fun is_bad_list [] = true
  | is_bad_list [_] = false
  | is_bad_list (p::q::ps) = if p = q then is_bad_list (q::ps) else true


(* transforms equations into the "p o c == c"-form 
   from p o (c x1 ...xn) = c (p o x1) ... (p o xn) *)

fun eqvt_transform_eq_tac thm = 
let
  val ss_thms = @{thms permute_minus_cancel permute_prod.simps split_paired_all}
in
  REPEAT o FIRST' 
    [CHANGED o simp_tac (HOL_basic_ss addsimps ss_thms),
     rtac (thm RS @{thm trans}),
     rtac @{thm trans[OF permute_fun_def]} THEN' rtac @{thm ext}]
end

fun eqvt_transform_eq ctxt thm = 
  let
    val (lhs, rhs) = HOLogic.dest_eq (HOLogic.dest_Trueprop (prop_of thm))
      handle TERM _ => error "Equivariance lemma must be an equality."
    val (p, t) = dest_perm lhs 
      handle TERM _ => error "Equivariance lemma is not of the form p \<bullet> c...  = c..."

    val ps = get_perms rhs handle TERM _ => []  
    val (c, c') = (head_of t, head_of rhs)
    val msg = "Equivariance lemma is not of the right form "
  in
    if c <> c' 
      then error (msg ^ "(constants do not agree).")
    else if is_bad_list (p :: ps)  
      then error (msg ^ "(permutations do not agree).") 
    else if not (rhs aconv (add_perm p t))
      then error (msg ^ "(arguments do not agree).")
    else if is_Const t 
      then safe_mk_equiv thm
    else 
      let 
        val goal = HOLogic.mk_Trueprop (HOLogic.mk_eq (mk_perm p c, c))
        val ([goal', p'], ctxt') = Variable.import_terms false [goal, p] ctxt
      in
        Goal.prove ctxt [] [] goal' (fn _ => eqvt_transform_eq_tac thm 1)
        |> singleton (Proof_Context.export ctxt' ctxt)
        |> safe_mk_equiv
        |> zero_var_indexes
      end
  end

(* transforms equations into the "p o c == c"-form 
   from R x1 ...xn ==> R (p o x1) ... (p o xn) *)

fun eqvt_transform_imp_tac ctxt p p' thm = 
  let
    val thy = Proof_Context.theory_of ctxt
    val cp = Thm.cterm_of thy p
    val cp' = Thm.cterm_of thy (mk_minus p')
    val thm' = Drule.cterm_instantiate [(cp, cp')] thm
    val simp = HOL_basic_ss addsimps @{thms permute_minus_cancel(2)}
  in
    EVERY' [rtac @{thm iffI}, dtac @{thm permute_boolE}, rtac thm, atac,
      rtac @{thm permute_boolI}, dtac thm', full_simp_tac simp]
  end

fun eqvt_transform_imp ctxt thm =
  let
    val (prem, concl) = pairself HOLogic.dest_Trueprop (Logic.dest_implies (prop_of thm))
    val (c, c') = (head_of prem, head_of concl)
    val ps = get_perms concl handle TERM _ => []  
    val p = try hd ps
    val msg = "Equivariance lemma is not of the right form "
  in
    if c <> c' 
      then error (msg ^ "(constants do not agree).")
    else if is_bad_list ps  
      then error (msg ^ "(permutations do not agree).") 
    else if not (concl aconv (add_perm (the p) prem)) 
      then error (msg ^ "(arguments do not agree).")
    else 
      let
        val prem' = mk_perm (the p) prem    
        val goal = HOLogic.mk_Trueprop (HOLogic.mk_eq (prem', concl))
        val ([goal', p'], ctxt') = Variable.import_terms false [goal, the p] ctxt
      in
        Goal.prove ctxt' [] [] goal'
          (fn _ => eqvt_transform_imp_tac ctxt' (the p) p' thm 1) 
        |> singleton (Proof_Context.export ctxt' ctxt)
      end
  end     

fun eqvt_transform ctxt thm = 
  case (prop_of thm) of
    @{const "Trueprop"} $ (Const (@{const_name "HOL.eq"}, _) $ 
      (Const (@{const_name "permute"}, _) $ _ $ _) $ _) => 
        eqvt_transform_eq ctxt thm
  | @{const "==>"} $ (@{const "Trueprop"} $ _) $ (@{const "Trueprop"} $ _) => 
      eqvt_transform_imp ctxt thm |> eqvt_transform_eq ctxt
  | _ => raise error "Only _ = _ and _ ==> _ cases are implemented."
 

(** attributes **)

val eqvt_add = Thm.declaration_attribute 
  (fn thm => fn context =>
   let
     val thm' = eqvt_transform (Context.proof_of context) thm
   in
     context |> add_thm thm |> add_raw_thm thm'
   end)

val eqvt_del = Thm.declaration_attribute
  (fn thm => fn context =>
   let
     val thm' = eqvt_transform (Context.proof_of context) thm
   in
     context |> del_thm thm  |> del_raw_thm thm'
   end)

val eqvt_raw_add = Thm.declaration_attribute add_raw_thm;
val eqvt_raw_del = Thm.declaration_attribute del_raw_thm;


(** setup function **)

val setup =
  Attrib.setup @{binding "eqvt"} (Attrib.add_del eqvt_add eqvt_del) 
    (cat_lines ["Declaration of equivariance lemmas - they will automtically be",  
       "brought into the form p o c == c"]) #>
  Attrib.setup @{binding "eqvt_raw"} (Attrib.add_del eqvt_raw_add eqvt_raw_del) 
    (cat_lines ["Declaration of equivariance lemmas - no",
       "transformation is performed"]) #>
  Global_Theory.add_thms_dynamic (@{binding "eqvts"}, eqvts) #>
  Global_Theory.add_thms_dynamic (@{binding "eqvts_raw"}, eqvts_raw);


end;
