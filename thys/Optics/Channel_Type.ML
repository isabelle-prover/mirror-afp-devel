structure Channel_Type =
struct
fun prove_prism_goal thy =
  let 
    val ctx = Named_Target.theory_init thy
 in
  auto_tac (fold Simplifier.add_simp (Global_Theory.get_thms thy Lens_Lib.lens_defsN) ctx)
end

val wb_prism_suffix = "_wb_prism"
val codep_suffix = "_codeps"

val ctor_suffix = "_C"

fun wb_prism_proof x thms ctx =
  Goal.prove ctx [] []
  (Syntax.check_term ctx (Prism_Lib.mk_wb_prism (Syntax.free x)))
  (fn {context = context, prems = _}
                       => EVERY [ PARALLEL_ALLGOALS (full_simp_tac (fold Simplifier.add_simp thms context))
                                , Classical.rule_tac context [@{thm wb_ctor_prism_intro}] [] 1
                                , auto_tac (context delsimprocs [@{simproc unit_eq}])
                                ])

fun codep_proof thms ctx (x, y) =
  Goal.prove ctx [] []
      (Syntax.check_term ctx (Prism_Lib.mk_codep (Syntax.free x) (Syntax.free y)))
      (fn {context = context, prems = _}
                           => EVERY [ PARALLEL_ALLGOALS (full_simp_tac (fold Simplifier.add_simp thms context))
                                    , Classical.rule_tac context [@{thm ctor_codep_intro}] [] 1
                                    , auto_tac ctx
                                    ])



fun mk_def ty x v = Const ("Pure.eq", ty --> ty --> Term.propT) $ Free (x, ty) $ v;

val is_prefix = "is_";
val un_prefix = "un_";

fun def qual (x, tm) ctx = 
  let 
    val ((_, (_, thm)), d) =
      Specification.definition (SOME (Binding.qualify false qual (Binding.name x), NONE, NoSyn)) [] [] ((Binding.empty, [Attrib.check_src @{context} (Token.make_src ("lens_defs", Position.none) [])]), mk_def dummyT x tm) ctx
  in (thm, d) end


fun defs qual inds f ctx =
  fold (fn i => fn (thms, ctx) =>
        let val (thm, ctx') = def qual (i, f i) ctx 
        in (thms @ [thm], ctx') end) inds ([], ctx)

fun compile_chantype (name, chans) ctx =
  let 
    val ctrs = map (fn (n, t) => (((Binding.empty, Binding.name (n ^ ctor_suffix)), [(Binding.empty, t)]), Mixfix.NoSyn)) chans 
    val pnames = map fst chans
    val thypfx = 
      case (Named_Target.locale_of ctx) of
        SOME loc => loc ^ "." |
        NONE => Context.theory_base_name (Local_Theory.exit_global ctx) ^ "."
    val prefix = thypfx ^ name ^ "."
    val attrs = @{attributes [simp, code_unfold]}
    val dummy_disc = absdummy dummyT @{term True}
  in
  (BNF_FP_Def_Sugar.co_datatype_cmd BNF_FP_Rec_Sugar_Util.Least_FP BNF_LFP.construct_lfp 
       ((K Plugin_Name.default_filter, true), 
        [((((([],Binding.name name), Mixfix.NoSyn), ctrs), (Binding.empty, Binding.empty, Binding.empty)),[])])
  (* The datatype package does not produce a discriminator for the second constructor when
     there are two constructors. We here generate one for uniformity. *)
  #> (if (length pnames = 2)
      then Specification.abbreviation 
             Syntax.mode_default (SOME (Binding.qualify false name (Binding.name (is_prefix ^ nth pnames 1 ^ ctor_suffix)), NONE, NoSyn)) [] 
             (mk_def dummyT 
                (is_prefix ^ nth pnames 1 ^ ctor_suffix) 
                (Syntax.const @{const_name comp} $ @{term Not} $ Syntax.const (prefix ^ is_prefix ^ nth pnames 0 ^ ctor_suffix))) false
      else I)
  #> defs name pnames (fn x => (Syntax.const @{const_name ctor_prism}
                         $ Syntax.const (prefix ^ x ^ ctor_suffix)
                         $ (if (length pnames = 1) then dummy_disc else Syntax.const (prefix ^ is_prefix ^ x ^ ctor_suffix))
                         $ Syntax.const (prefix ^ un_prefix ^ x ^ ctor_suffix)))
  #> (fn (thms, ctx) =>
       (fold (fn x => fn thy => snd (Local_Theory.note ((Binding.qualify false name (Binding.name (x ^ wb_prism_suffix)), attrs), [wb_prism_proof x thms thy]) thy)) pnames
       #> (snd o Local_Theory.note ((Binding.qualify false name (Binding.name Prism_Lib.codepsN), attrs), map (codep_proof thms ctx) (Lens_Lib.pairings pnames)))
       ) ctx))
  ctx
  end;

val _ =
  Outer_Syntax.command @{command_keyword chantype} "define a channel datatype"
    ((Parse.name --
      (@{keyword "="} |-- Scan.repeat1 (Parse.name -- (Parse.$$$ "::" |-- Parse.!!! Parse.typ))))
    >> (fn x => Toplevel.local_theory NONE NONE (compile_chantype x)))

end;
