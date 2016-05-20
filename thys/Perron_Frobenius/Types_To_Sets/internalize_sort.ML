(*  Title:      internalize_sort.ML
    Author:     Ondřej Kunčar, TU München

    Wrapper around Thm.unconstrainT to internalize type classes.
    No new trusted code needed.
*)

signature INTERNALIZE_SORT =
sig
  val internalize_sort:  ctyp -> thm -> typ * thm
  val internalize_sort_attr: typ -> attribute
end

structure Internalize_Sort : INTERNALIZE_SORT =
struct

  fun internalize_sort ctvar thm =
    let
      val thy = Thm.theory_of_thm thm
      val ctxt = Proof_Context.init_global thy
      val tvar = Thm.typ_of ctvar
      
      val thm = Thm.strip_shyps thm

      val ((_, assms, classes),_) = Logic.unconstrainT [] (Thm.prop_of thm);
  
      fun is_proper_class thy = can (Axclass.get_info thy); (* trick by FH *)
      fun reduce_to_non_proper_sort (TVar (name, sort)) = 
        TVar (name, Sign.minimize_sort thy (filter_out (is_proper_class thy) (Sign.complete_sort thy sort)))
  
      val data = (map fst classes) ~~ assms;
      
      val new_tvar = get_first (fn (tvar', ((ren_tvar, _), _)) => if tvar = tvar' 
        then SOME (reduce_to_non_proper_sort ren_tvar) else NONE) data
        |> the_default tvar
      
      fun add_non_proper_sort (TVar (name, _)) assm = 
        Term_Subst.instantiate ([((name,[]), new_tvar)], []) assm |> Thm.cterm_of ctxt |> Thm.trivial
      
      fun localify class =
        Class.rules thy class |> snd |> Thm.transfer thy
  
      val rules = map (fn (tvar', ((ren_tvar, class), assm)) => if tvar = tvar' 
        then (if Class.is_class thy class then localify class else add_non_proper_sort ren_tvar assm)
        else Thm.of_class (Thm.ctyp_of ctxt ren_tvar, class)) data;
    in
      (new_tvar, (Thm.unconstrainT thm OF rules) |> Drule.zero_var_indexes)
    end;

  val parse_schematic_type_variable = Args.context -- Scan.lift Parse.typ >> 
    (fn (ctxt, str) => 
    let
      val ctxt = Proof_Context.set_mode Proof_Context.mode_schematic ctxt
    in
     Syntax.read_typ ctxt str 
    end)
  
  val tvar = Args.context -- parse_schematic_type_variable >> (fn (_, v as TVar _) => v | (ctxt, t) =>
    error ("Bad schematic type variable: " ^ Syntax.string_of_typ ctxt t));

  fun internalize_sort_attr tvar = 
    Thm.rule_attribute [] (fn context => fn thm => 
      (snd (internalize_sort (Thm.ctyp_of (Context.proof_of context) tvar) thm)));

  val _ = Context.>> (Context.map_theory (Attrib.setup @{binding internalize_sort} 
    (tvar >> internalize_sort_attr) "internalizes a sort"))
end