\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory Cases_Tactics_HOL
  imports
    Cases_Tactics
    HOL.HOL
begin

ML\<open>
structure Cases_Tactic_HOL = Cases_Tactic(open Induct
  fun get_casesP ctxt (fact :: _) = find_casesP ctxt (Thm.concl_of fact)
    | get_casesP _ _ = []
  fun get_casesT ctxt binderTs (SOME t :: _) = find_casesT ctxt (Term.fastype_of1 (binderTs, t))
  | get_casesT _ _ _ = [])
structure Cases_Data_Args_Tactic_HOL = Cases_Data_Args_Tactic(Cases_Tactic_HOL)
\<close>

text \<open>For a function \<open>f :: T\<^sub>1 \<Rightarrow> \<dots> \<Rightarrow> T\<^sub>n \<Rightarrow> T\<close> with multiple arguments, the function package creates a
cases rule \<open>f.cases\<close> where \<open>f\<close>'s arguments are tupled and equated to a single variable. As a result,
one has to supply the cases tactic a single instantiation \<open>(t\<^sub>1,\<dots>,t\<^sub>n)\<close> when using \<open>f.cases\<close> while
users would expect being able to supply \<open>n\<close> instantiations \<open>t\<^sub>1,\<dots>,t\<^sub>n\<close>. Below attribute transforms
such rules to the expected form.\<close>

local_setup \<open>
  let
    fun add_prodTs T acc = try HOLogic.dest_prodT T
      |> (fn NONE => T :: acc | SOME (T, T') => T :: add_prodTs T' acc)
    fun inst_prod_cases ctxt thm = case Thm.prop_of thm |> Term.add_vars |> build |> rev of
        [] => error "No schematic variable in passed cases theorem."
      | ((n, _), T) :: _ =>
        let
          val maxidx = Thm.maxidx_of thm
          val inst = build (add_prodTs T)
            |> map_index (fn (idx, T) => Var ((n, maxidx + idx + 1), T))
            |> rev
            |> (fn t :: ts => fold (curry HOLogic.mk_prod) ts t)
            |> Thm.cterm_of ctxt
        in Thm.instantiate' [] [SOME inst] thm end
  in
    Attrib.local_setup @{binding deprod_cases}
      (Scan.succeed (Thm.rule_attribute [] (Context.proof_of #> inst_prod_cases)))
      ("Transform cases rule that uses a single product for instantiation to a cases rule using "
        ^ "multiple instantiations.")
  end
\<close>

end