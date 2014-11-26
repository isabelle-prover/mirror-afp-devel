theory Indep_Vars
imports Main Refine_Util Mpat_Antiquot
begin

definition [simp]: "INDEP v \<equiv> True"
lemma INDEPI: "INDEP v" by simp

ML {*
  signature INDEP_VARS = sig
    val indep_tac: tactic'
  end

  structure Indep_Vars :INDEP_VARS = struct

    local
      fun vsubterms (Abs (_,_,t)) = vsubterms t
        | vsubterms (t as (_$_)) = let
            val (f,args) = strip_comb t
            val args_vsts = map vsubterms args |> flat
          in 
            case f of 
              (Var (name,vT)) => [(name,vT,fastype_of t,args)]@args_vsts
            | _ => vsubterms f @ args_vsts
          end
        | vsubterms _ = []

      fun indep_vars t st = let
        val thy = theory_of_thm st
        val cert = cterm_of thy

        fun inst_of (name,vT,T,args) = let
          val Ts = map fastype_of args |> rev
          val t' = fold absdummy Ts (Var (name,T))
          val inst = (cert (Var (name,vT)), cert t')
        in inst end

        val inst = vsubterms t
          |> distinct (op = o apply2 #1)
          |> map inst_of

        val st' = Drule.instantiate_normalize ([],inst) st
          |> Conv.fconv_rule (Thm.beta_conversion true)
      in 
        Seq.single st' 
      end
      
      fun indep_tac_aux i st = case Logic.concl_of_goal (prop_of st) i of
        @{mpat "Trueprop (INDEP ?v)"} 
          => (indep_vars v THEN rtac @{thm INDEPI} i) st
      | _ => Seq.empty

    in
      (* Remove explicit parameters from schematic variable. *)
      val indep_tac = IF_EXGOAL 
        (CONVERSION Thm.eta_conversion THEN' indep_tac_aux)
    end
  end
*}


(*schematic_lemma 
  "!!x y z. INDEP (?R x z)"
  "!!x y z. ?R x z 1"
  apply (tactic {* Indep_Vars.indep_tac 1 *})
  apply rule
  done
*)



end

(*

      fun indep_vars t st = case strip_comb t of
        (v as Var (name,_),args) => let
          val thy = theory_of_thm st
          val cert = cterm_of thy
  
          val T = fastype_of t
          val Ts = map fastype_of args |> rev
          val t' = fold absdummy Ts (Var (name,T))
          val inst = ([],[(cert v, cert t')]) handle e =>
            ( tracing (Syntax.pretty_term_global thy t |> Pretty.string_of);
              reraise e
            )

          val st' = Drule.instantiate_normalize inst st
            |> Conv.fconv_rule (Thm.beta_conversion true)

          val _ = Config.get_global thy cfg_trace andalso (Pretty.block [
            Pretty.str "INDEP ", Syntax.pretty_term_global thy t, 
              Pretty.brk 1, Pretty.str ":", Pretty.brk 1,
              Syntax.pretty_term_global thy v,
              Pretty.brk 1, Pretty.str "->", Pretty.brk 1,
              Syntax.pretty_term_global thy t',
              Pretty.fbrk,
              Pretty.indent 2 (
                Pretty.big_list "Goals: " 
                  (Goal_Display.pretty_goals_without_context st'))
          ] |> Pretty.string_of |> tracing; true)

        in Seq.single st' end
      | _ => (
        Pretty.block [ 
            Pretty.str "INDEP on non-variable: ", 
            Syntax.pretty_term_global (theory_of_thm st) t
          ] |> Pretty.string_of |> warning;
        Seq.single st
      )



  Old version: Removes all functionality, not only explicit parameters
  structure Indep_Vars :INDEP_VARS = struct
    local
      (* Remove explicit parameters from relation variable. *)
      fun indep_var (name,typ) = let
        val (Ts,T) = strip_type typ |>> rev
        val r = fold absdummy Ts (Var (name,T))
      in 
        r
      end

      fun indep_vars R st = let
        val vs = Term.add_vars R []
        val cert = cterm_of (theory_of_thm st)
        val inst = map (fn v => (cert (Var v), cert (indep_var v))) vs
        val st' = Drule.instantiate_normalize ([],inst) st
          |> Conv.fconv_rule (Thm.beta_conversion true)
      in 
        Seq.single st'
      end

      fun indep_tac_aux i st = case Logic.concl_of_goal (prop_of st) i of
        @{mpat "Trueprop (INDEP ?v)"} 
          => (indep_vars v THEN rtac @{thm INDEPI} i) st
      | _ => Seq.empty

    in
      val indep_tac = IF_EXGOAL indep_tac_aux

    end
  end



*)
