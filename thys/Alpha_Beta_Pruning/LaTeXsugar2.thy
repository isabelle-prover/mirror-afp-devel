theory LaTeXsugar2
imports
  Prog_Prove.LaTeXsugar
begin

definition mbox :: "'a \<Rightarrow> 'a" where
"mbox x = x"

definition mbox0 :: "'a \<Rightarrow> 'a" where
"mbox0 x = x"

notation (latex) mbox (\<open>\<^latex>\<open>\mbox{\<close>_\<^latex>\<open>}\<close>\<close> [999] 999)

notation (latex) mbox0 (\<open>\<^latex>\<open>\mbox{\<close>_\<^latex>\<open>}\<close>\<close> [0] 999)

(* Parenthesize conjunctions to the left; otherwise, if a larger conjunction needs a line break,
the pretty printer will put the first few conjuncts on separate lines until the rest fits. *)
syntax (output)
  "_conjL" :: "bool \<Rightarrow> bool \<Rightarrow> bool" (infixl \<open>\<and>\<close> 35)
syntax (latex output)
  "_conjL" :: "bool \<Rightarrow> bool \<Rightarrow> bool" (infixl \<open>\<and>\<close> 35)
translations
  "_conjL P Q" <= "P \<and> Q" 
  "_conjL (_conjL P Q) R" <= "_conjL P (_conjL Q R)"
(* The above regrouping of conjunctions may have the opposite effect, the last few conjuncts ending up
on separate lines. However, it appears beneficial in the majority of cases *)

(* For manual regrouping with invisible blocks: *)
definition BLOCK where [simp]: "BLOCK x = x"
notation (output) BLOCK (\<open>_\<close>)

(* Forced parentheses *)
definition parens where
  "parens x = x"

notation (output) parens (\<open>\<^bold>'(_\<^bold>')\<close>)

notation (latex output) parens
  (\<open>'(_')\<close>)

no_notation (output)
  HOL.eq (infix \<open>=\<close> 50)

notation (output)
  HOL.eq (\<open>(_/ = _)\<close> [51,51] 50)

notation (latex output)
  If  (\<open>(\<^latex>\<open>\isakeyword{\<close>if\<^latex>\<open>}\<close> (_)/ \<^latex>\<open>\isakeyword{\<close>then\<^latex>\<open>}\<close> (_)/ \<^latex>\<open>\isakeyword{\<close>else\<^latex>\<open>}\<close> (_))\<close> 10)

syntax (latex output)

  "_Let"        :: "[letbinds, 'a] => 'a"
  (\<open>(\<^latex>\<open>\isakeyword{\<close>let\<^latex>\<open>}\<close> (_)/ \<^latex>\<open>\isakeyword{\<close>in\<^latex>\<open>}\<close> (_))\<close> 10)

  "_case_syntax":: "['a, cases_syn] => 'b"
  (\<open>(\<^latex>\<open>\isakeyword{\<close>case\<^latex>\<open>}\<close> _ \<^latex>\<open>\isakeyword{\<close>of\<^latex>\<open>}\<close>/ _)\<close> 10)

syntax (let_break output)

  "_binds" :: "[letbind, letbinds] \<Rightarrow> letbinds"  (\<open>_;//_\<close>)

syntax (case_break output)

  "_case2" :: "[case_syn, cases_syn] \<Rightarrow> cases_syn"  (\<open>_ |//_\<close>)

  "_case_syntax":: "['a, cases_syn] => 'b"
  (\<open>(\<^latex>\<open>\isakeyword{\<close>case\<^latex>\<open>}\<close> _ \<^latex>\<open>\isakeyword{\<close>of\<^latex>\<open>}\<close>//_)\<close> 10)

abbreviation (iffSpace)
  iffSpace :: "[bool, bool] => bool"  (infixr \<open>\<^latex>\<open>\ \<close>\<longleftrightarrow>\<^latex>\<open>\ \<close>\<close> 25)
where
  "iffSpace A B == A = B"

ML \<open>
fun dummy_pats_style (wrap $ (eq $ lhs $ rhs)) =
  let
    val rhs_vars = Term.add_vars rhs [];
    fun dummy (v as Var (ixn as (_, T))) =
          if member ((=) ) rhs_vars ixn then v else Const (@{const_name DUMMY}, T)
      | dummy (t $ u) = dummy t $ dummy u
      | dummy (Abs (n, T, b)) = Abs (n, T, dummy b)
      | dummy t = t;
  in wrap $ (eq $ dummy lhs $ rhs) end
\<close>

setup\<open>
Term_Style.setup @{binding dummy_pats} (Scan.succeed (K dummy_pats_style))
\<close>

(* Dummy vars on lhs in case expressions: *)
syntax (output)
  "_case1'" :: "['a, 'b] \<Rightarrow> case_syn"  (\<open>(2_ \<Rightarrow>/ _)\<close> 10)

print_ast_translation \<open>
  let
    fun vars (Ast.Constant _) = []
      | vars (Ast.Variable x) = [x]
      | vars (Ast.Appl ts) = flat(map vars ts);
    fun dummy vs (Ast.Appl ts) = Ast.Appl(map (dummy vs) ts)
      | dummy vs (Ast.Variable x) = Ast.Variable (if member (op =) vs x then x else "_")
      | dummy _ c = c
    fun case1_tr' [l,r] =
          Ast.Appl [Ast.Constant @{syntax_const "_case1'"}, dummy (vars r) l, r]
  in [(\<^syntax_const>\<open>_case1\<close>, K case1_tr')] end
\<close>

setup \<open>
let

fun eta_expand Ts t xs = case t of
    Abs(x,T,t) =>
      let val (t', xs') = eta_expand (T::Ts) t xs
      in (Abs (x, T, t'), xs') end
  | _ =>
      let
        val (a,ts) = strip_comb t (* assume a atomic *)
        val (ts',xs') = fold_map (eta_expand Ts) ts xs
        val Bs = binder_types (fastype_of1 (Ts,t));
        val n = Int.min (length Bs, length xs');
        val bs = map Bound ((n - 1) downto 0);
        val xBs = ListPair.zip (xs',Bs);
        val xs'' = drop n xs';
        val t' = incr_boundvars n (list_comb (a, ts'));
        val t'' = fold_rev Term.abs xBs (list_comb(t', bs))
      in (t'', xs'') end

val style_eta_expand =
  (Scan.repeat Args.name) >> (fn xs => fn ctxt => fn t => fst (eta_expand [] t xs))

in Term_Style.setup @{binding eta_expand} style_eta_expand end
\<close>

ML \<open>
fun pretty_const_typ ctxt (c, maybe_typ) : Pretty.T =
  (*taken from Prog_Prove/LaTeXsugar.thy*)
  let
    val tc = Proof_Context.read_const {proper = true, strict = false} ctxt c
    val pretty_typ =
      (case maybe_typ of
        NONE => Syntax.pretty_typ ctxt (fastype_of tc)
      | SOME typ =>
        let val typ_instance = Type.typ_instance o Proof_Context.tsig_of in
          if typ_instance ctxt (typ, fastype_of tc) then Syntax.pretty_typ ctxt typ
          else error ("constant " ^ quote (Proof_Context.markup_const ctxt c) ^ " is not of type " ^
            quote (Syntax.string_of_typ ctxt typ))
        end)
  in
    Pretty.block [Document_Output.pretty_term ctxt tc, Pretty.str " ::",
    Pretty.brk 1, pretty_typ]
  end

fun pretty_eqs_style f ctxt (style, (name, maybe_thms)) : Pretty.T =
  let val eq = Document_Output.pretty_term ctxt o style o Thm.full_prop_of
  in
    (case maybe_thms of
      SOME thms => map eq thms |> Pretty.chunks
    | NONE =>
      f name
      |> Proof_Context.get_thms ctxt
      |> map eq
      |> Pretty.chunks)
  end

fun separate_texts (sep: Latex.text) (texts: Latex.text list) : Latex.text =
  separate sep texts |> List.concat

fun pretty_funs_style_generic f ctxt (style, names) : Latex.text =
  names
  |> map (fn ((name, typ), eqs) =>
    let
      val thy_output = Document_Output.pretty ctxt
      val equations = pretty_eqs_style f ctxt (dummy_pats_style o style, (name, eqs)) |> thy_output
      val header = pretty_const_typ ctxt (name, typ) |> thy_output
    in separate_texts (Latex.string "\\\\[\\funheadersep]" ) [header, equations] end)
  |> separate_texts (Latex.string "\\\\\\\\")
  |> XML.enclose "{\\parindent0pt" "}"

fun pretty_custom_funs_style_generic f ctxt (style, names) : Latex.text =
  names
  |> map (fn ((name, typ), eqs) =>
    let
      val thy_output = Document_Output.pretty ctxt
      val equations = pretty_eqs_style f ctxt (dummy_pats_style o style, (name, eqs)) |> thy_output
      val header = pretty_const_typ ctxt (name, typ) |> thy_output
    in separate_texts (Latex.string "\\\\[\\funheadersep]" ) [header, equations] end)
  |> separate_texts (Latex.string "\\\\\\\\")
  |> XML.enclose "{\\parindent0pt" "}"
\<close>

setup \<open>
let val parse =
  Args.const {proper = true, strict = false} --
  Scan.option (Scan.lift (Args.$$$ "::") |-- Args.typ) --
  Scan.option (Scan.lift (Args.$$$ "[") |-- Attrib.thms --| Scan.lift (Args.$$$ "]"))
in
  Document_Output.antiquotation_raw \<^binding>\<open>def\<close>
    (Term_Style.parse -- Parse.and_list1' parse)
      (Config.put Document_Antiquotation.thy_output_break true
      #> pretty_funs_style_generic (fn n => n ^ "_def"))
  #> Document_Output.antiquotation_raw \<^binding>\<open>fun\<close>
    (Term_Style.parse -- Parse.and_list1' parse)
      (Config.put Document_Antiquotation.thy_output_break true
      #> pretty_funs_style_generic (fn n => n ^ ".simps"))
end
\<close>

end
