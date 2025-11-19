section \<open>Setup for Experiments\<close>

theory Test_Pat_Complete
  imports 
    Pattern_Completeness
    "HOL-Library.Code_Abstract_Char"
    "HOL-Library.Code_Target_Numeral"
    "HOL-Library.RBT_Mapping" 
    "HOL-Library.Product_Lexorder" 
    "HOL-Library.List_Lexorder" 
    "Show.Number_Parser" 
begin

subsection \<open>FSCD paper\<close>

text \<open>turn error message into runtime error\<close>
definition pat_complete_alg_fscd :: "(('f \<times> 's list) \<times> 's)list \<Rightarrow> (('f \<times> 's list) \<times> 's)list \<Rightarrow> ('f,'v)term list \<Rightarrow> bool" where 
  "pat_complete_alg_fscd C D lhss = (
  case decide_pat_complete_lhss_fscd C D lhss of Inl err \<Rightarrow> Code.abort (err (STR '''')) (\<lambda> _. True)
    | Inr res \<Rightarrow> res)" 

text \<open>turn error message into runtime error\<close>
definition strong_quasi_reducible_alg :: "_ \<Rightarrow> _ \<Rightarrow> (('f \<times> 's list) \<times> 's)list \<Rightarrow> (('f \<times> 's list) \<times> 's)list \<Rightarrow> ('f,'v)term list \<Rightarrow> bool" where 
  "strong_quasi_reducible_alg rn rv C D lhss = (
  case decide_strong_quasi_reducible rn rv C D lhss of Inl err \<Rightarrow> Code.abort (err (STR '''')) (\<lambda> _. True)
    | Inr res \<Rightarrow> res)" 

text \<open>Examples\<close>
definition "nat_bool = [ 
   ((''zero'', []), ''nat''),
   ((''succ'', [''nat'']), ''nat''),
   ((''true'', []), ''bool''),
   ((''false'', []), ''bool'')
   ]"

definition rn_string where "rn_string x = ''x'' @ show (x :: nat)"
definition rv_string where "rv_string x = ''y'' @ x"

lemma renaming_string: "renaming_funs rn_string rv_string"
  using inj_show_nat 
  unfolding renaming_funs_def 
  by (auto simp: inj_def rn_string_def rv_string_def) 

definition "decide_pat_complete_lhss_string = decide_pat_complete_lhss rn_string rv_string" 
definition "decide_strong_qd_lhss_string = decide_strong_quasi_reducible rn_string rv_string" 

lemmas decide_pat_complete_lhss_string = decide_pat_complete_lhss[OF _ renaming_string,
    folded decide_pat_complete_lhss_string_def]

lemmas decide_strong_qd_lhss_string = decide_strong_quasi_reducible[OF _ renaming_string,
    folded decide_strong_qd_lhss_string_def]

definition "int_bool = [ 
   ((''zero'', []), ''int''),
   ((''succ'', [''int'']), ''int''),
   ((''pred'', [''int'']), ''int''),
   ((''true'', []), ''bool''),
   ((''false'', []), ''bool'')
   ]"

definition "even_nat = [
    ((''even'', [''nat'']), ''bool'')
  ]" 

definition "even_int = [
    ((''even'', [''int'']), ''bool'')
  ]" 

definition "even_lhss = [
  Fun ''even'' [Fun ''zero'' []],
  Fun ''even'' [Fun ''succ'' [Fun ''zero'' []]],
  Fun ''even'' [Fun ''succ'' [Fun ''succ'' [Var ''x'']]]
  ]"

definition "even_lhss_int = [
  Fun ''even'' [Fun ''zero'' []],
  Fun ''even'' [Fun ''succ'' [Fun ''zero'' []]],
  Fun ''even'' [Fun ''succ'' [Fun ''succ'' [Var ''x'']]],
  Fun ''even'' [Fun ''pred'' [Fun ''zero'' []]],
  Fun ''even'' [Fun ''pred'' [Fun ''pred'' [Var ''x'']]],
  Fun ''succ'' [Fun ''pred'' [Var ''x'']],
  Fun ''pred'' [Fun ''succ'' [Var ''x'']]
  ]"

lemma decide_pat_complete_wrapper_fscd: 
  assumes "(case decide_pat_complete_lhss_fscd C D lhss of Inr b \<Rightarrow> Some b | Inl _ \<Rightarrow> None) = Some res"
  shows "pat_complete_lhss (map_of C) (map_of D) (set lhss) = res" 
  using decide_pat_complete_lhss_fscd[of C D lhss] assms by (auto split: sum.splits)

lemma decide_pat_complete_wrapper: 
  assumes "(case decide_pat_complete_lhss_string C D lhss of Inr b \<Rightarrow> Some b | Inl _ \<Rightarrow> None) = Some res"
  shows "pat_complete_lhss (map_of C) (map_of D) (set lhss) = res" 
  using decide_pat_complete_lhss_string[of C D lhss] assms by (auto split: sum.splits)

lemma decide_strong_quasi_reducible_wrapper: 
  assumes "(case decide_strong_qd_lhss_string C D lhss of Inr b \<Rightarrow> Some b | Inl _ \<Rightarrow> None) = Some res"
  shows "strong_quasi_reducible (map_of C) (map_of D) (set lhss) = res" 
  using decide_strong_qd_lhss_string[of C D lhss] assms by (auto split: sum.splits)

lemma "pat_complete_lhss (map_of nat_bool) (map_of even_nat) (set even_lhss)"
  apply (subst decide_pat_complete_wrapper_fscd[of _ _ _ True])
  by eval+

lemma "\<not> pat_complete_lhss (map_of int_bool) (map_of even_int) (set even_lhss_int)" 
  apply (subst decide_pat_complete_wrapper_fscd[of _ _ _ False])
  by eval+

value "decide_pat_complete_linear_lhss int_bool even_int even_lhss_int" 


lemma "strong_quasi_reducible (map_of int_bool) (map_of even_int) (set even_lhss_int)" 
  apply (subst decide_strong_quasi_reducible_wrapper[of _ _ _ True])
  by eval+


definition "non_lin_lhss = [
  Fun ''f'' [Var ''x'', Var ''x'', Var ''y''],
  Fun ''f'' [Var ''x'', Var ''y'', Var ''x''],
  Fun ''f'' [Var ''y'', Var ''x'', Var ''x'']
  ]"

lemma "pat_complete_lhss (map_of nat_bool) (map_of [((''f'',[''bool'',''bool'',''bool'']),''bool'')]) (set non_lin_lhss)" 
  apply (subst decide_pat_complete_wrapper_fscd[of _ _ _ True])
  by eval+

lemma "\<not> pat_complete_lhss (map_of nat_bool) (map_of [((''f'',[''nat'',''nat'',''nat'']),''bool'')]) (set non_lin_lhss)" 
  apply (subst decide_pat_complete_wrapper_fscd[of _ _ _ False])
  by eval+

(* the algorithm for linear lhss returns a wrong result here; the reason is that 
   it does not check that the input is indeed linear *)
value "decide_pat_complete_linear_lhss nat_bool [((''f'',[''nat'',''nat'',''nat'']),''bool'')] non_lin_lhss" 

(* the algorithm from the journal submission can of course also be used for the non-linear problems *)
lemma "pat_complete_lhss (map_of nat_bool) (map_of even_nat) (set even_lhss)" 
  apply (subst decide_pat_complete_wrapper[of _ _ _ True])
  by eval+

lemma "\<not> pat_complete_lhss (map_of nat_bool) (map_of [((''f'',[''nat'',''nat'',''nat'']),''bool'')]) (set non_lin_lhss)" 
  apply (subst decide_pat_complete_wrapper[of _ _ _ False])
  by eval+

lemma "pat_complete_lhss (map_of nat_bool) (map_of [((''f'',[''bool'',''bool'',''bool'']),''bool'')]) (set non_lin_lhss)" 
  apply (subst decide_pat_complete_wrapper[of _ _ _ True])
  by eval+


definition "testproblem (c :: nat) n = (let s = String.implode; s = id;
    c1 = even c;
    c2 = even (c div 2);
    c3 = even (c div 4);
    c4 = even (c div 8);
    revo = (if c4 then id else rev);
    nn = [0 ..< n];
    rnn = (if c4 then id nn else rev nn);
    b = s ''b''; t = s ''tt''; f = s ''ff''; g = s ''g'';
    gg = (\<lambda> ts. Fun g (revo ts));
    ff = Fun f [];
    tt = Fun t [];
    C = [((t, [] :: string list), b), ((f, []), b)];
    D = [((g, replicate (2 * n) b), b)];
    x = (\<lambda> i :: nat. Var (s (''x'' @ show i)));
    y = (\<lambda> i :: nat. Var (s (''y'' @ show i)));
    lhsF = gg (if c1 then List.maps (\<lambda> i. [ff, y i] ) rnn else (replicate n ff @ map y rnn));
    lhsT = (\<lambda> b j. gg (if c1 then List.maps (\<lambda> i. if i = j then [tt, b] else [x i, y i] ) rnn else 
             (map (\<lambda> i. if i = j then tt else x i) rnn @ map (\<lambda> i. if i = j then b else y i) rnn)));
    lhssT = (if c2 then List.maps (\<lambda> i. [lhsT tt i, lhsT ff i]) nn else List.maps (\<lambda> b. map (lhsT b) nn) [tt,ff]); 
    lhss = (if c3 then [lhsF] @ lhssT else lhssT @ [lhsF])
  in (C, D, lhss))"

definition "test_problem c n perms = (if c < 16 then testproblem c n
  else let (C, D, lhss) = testproblem 0 n;
      (permRow,permCol) = perms ! (c - 16);
      permRows = map (\<lambda> i. lhss ! i) permRow;
      pCol = (\<lambda> t. case t of Fun g ts \<Rightarrow> Fun g (map (\<lambda> i. ts ! i) permCol))
    in (C, D, map pCol permRows))" 

definition test_problem_integer where 
  "test_problem_integer c n perms = test_problem (nat_of_integer c) (nat_of_integer n) (map (map_prod (map nat_of_integer) (map nat_of_integer)) perms)" 

fun term_to_haskell where
  "term_to_haskell (Var x) = String.implode x" 
| "term_to_haskell (Fun f ts) = (if f = ''tt'' then STR ''TT'' else if f = ''ff'' then STR ''FF'' else String.implode f)
    + foldr (\<lambda> t r. STR '' '' + term_to_haskell t + r) ts (STR '''')" 

definition createHaskellInput :: "integer \<Rightarrow> integer \<Rightarrow> (integer list \<times> integer list) list \<Rightarrow> String.literal" where
  "createHaskellInput c n perms = (case test_problem_integer c n perms 
    of 
    (_,_,lhss) \<Rightarrow> STR ''module Test(g) where\<newline>\<newline>data B = TT | FF\<newline>\<newline>'' + 
      foldr (\<lambda> l s. (term_to_haskell l + STR '' = TT\<newline>'' + s)) lhss (STR ''''))" 

definition pat_complete_alg_test_fscd :: "integer \<Rightarrow> integer \<Rightarrow> (integer list * integer list)list \<Rightarrow> bool" where
  "pat_complete_alg_test_fscd c n perms = (case test_problem_integer c n perms of 
    (C,D,lhss) \<Rightarrow> pat_complete_alg_fscd C D lhss)" 

definition show_pat_complete_test :: "integer \<Rightarrow> integer \<Rightarrow> (integer list * integer list)list \<Rightarrow> String.literal" where
  "show_pat_complete_test c n perms = (case test_problem_integer c n perms of (_,_,lhss) 
  \<Rightarrow> showsl_lines (STR ''empty'') lhss (STR ''''))" 

definition create_agcp_input :: "(String.literal \<Rightarrow> 't) \<Rightarrow> integer \<Rightarrow> integer \<Rightarrow> (integer list * integer list)list \<Rightarrow>
  't list list * 't list list" where
  "create_agcp_input term C N perms = (let 
      n = nat_of_integer N; 
      c = nat_of_integer C;
      lhss = (snd o snd) (test_problem_integer C N perms);
      tt = (\<lambda> t. case t of (Var x) \<Rightarrow> term (String.implode (''?'' @ x @ '':B''))
           | Fun f [] \<Rightarrow> term (String.implode f));
      pslist = map (\<lambda> i. tt (Var (''x'' @ show i))) [0..< 2 * n];
      
      patlist = map (\<lambda> t. case t of Fun _ ps \<Rightarrow> map tt ps) lhss
    in ([pslist], patlist))"


text \<open>tree automata encoding\<close>

text \<open>We assume that there are certain interface-functions from the tree-automata library.\<close>
context
  fixes cState :: "String.literal \<Rightarrow> 'state" \<comment> \<open>create a state from name\<close>
  and cSym :: "String.literal \<Rightarrow> integer \<Rightarrow> 'sym" \<comment> \<open>create a symbol from name and arity\<close>
  and cRule :: "'sym \<Rightarrow> 'state list \<Rightarrow> 'state \<Rightarrow> 'rule" \<comment> \<open>create a transition-rule\<close>
  and cAut :: "'sym list \<Rightarrow> 'state list \<Rightarrow> 'state list \<Rightarrow> 'rule list \<Rightarrow> 'aut" 
    \<comment> \<open>create an automaton given the signature, the list of all states, the list of final states,
        and the transitions\<close>
  and checkSubset :: "'aut \<Rightarrow> 'aut \<Rightarrow> bool" \<comment> \<open>check language inclusion\<close>
begin

text \<open>we further fix the parameters to generate the example TRSs\<close>
context
  fixes c n :: integer
  and perms :: "(integer list \<times> integer list) list" 
begin

definition "tt = cSym (STR ''tt'') 0" 
definition "ff = cSym (STR ''ff'') 0" 
definition "g = cSym (STR ''g'') (2 * n)" 
definition "qt = cState (STR ''qt'')" 
definition "qf = cState (STR ''qf'')" 
definition "qb = cState (STR ''qb'')" 
definition "qfin = cState (STR ''qFin'')" 
definition "tRule = (\<lambda> q. cRule tt [] q)" 
definition "fRule = (\<lambda> q. cRule ff [] q)" 

definition "qbRules = [tRule qb, fRule qb]" 
definition "stdRules = qbRules @ [tRule qt, fRule qf]" 
definition "leftStates = [qb, qfin]" 
definition "rightStates = [qt, qf] @ leftStates" 
definition "finStates = [qfin]" 
definition "signature = [tt, ff, g]" 

fun argToState where 
  "argToState (Var _) = qb" 
| "argToState (Fun s []) = (if s = ''tt'' then qt else if s = ''ff'' then qf
     else Code.abort (STR ''unknown'') (\<lambda> _. qf))" 

fun termToRule where
  "termToRule (Fun _ ts) = cRule g (map argToState ts) qfin" 

definition "automataLeft = cAut signature leftStates finStates (cRule g (replicate (2 * nat_of_integer n) qb) qfin # qbRules)" 
definition "automataRight = (case test_problem_integer c n perms of 
  (_,_,lhss) \<Rightarrow> cAut signature rightStates finStates (map termToRule lhss @ stdRules))"

definition "encodeAutomata = (automataLeft, automataRight)" 

definition "patCompleteAutomataTest = (checkSubset automataLeft automataRight)" 
end
end

definition string_append :: "String.literal \<Rightarrow> String.literal \<Rightarrow> String.literal" (infixr \<open>+++\<close> 65) where
  "string_append s t = String.implode (String.explode s @ String.explode t)" 

code_printing constant string_append \<rightharpoonup>
  (Haskell)  infixr 5 "++"

fun paren where
  "paren e l r s [] = e" 
| "paren e l r s (x # xs) = l +++ x +++ foldr (\<lambda> y r. s +++ y +++ r) xs r" 

definition showAutomata where "showAutomata n c perms = (case encodeAutomata id (\<lambda> n a. n) 
  (\<lambda> f qs q. paren f (f +++ STR ''('') (STR '')'') (STR '','') qs +++ STR '' -> '' +++ q)
  (\<lambda> sig Q Qfin rls. 
     STR ''tree-automata has final states: '' +++ paren (STR ''{}'') (STR ''{'') (STR ''}'') (STR '','') Qfin +++ STR ''\<newline>'' 
     +++ STR ''and transitions:\<newline>'' +++ paren (STR '''') (STR '''') (STR '''') (STR ''\<newline>'') rls +++ STR ''\<newline>\<newline>'') n c perms
  of (all,pats) \<Rightarrow> STR ''decide whether language of first automaton is subset of the second automaton\<newline>\<newline>''
       +++ STR ''first '' +++ all +++ STR ''\<newline>and second '' +++ pats)" 

value "showAutomata 4 4 []" 

value "show_pat_complete_test 4 4 []" 

value "createHaskellInput 4 4 []" 


subsection \<open>Journal Submission\<close>

definition pat_complete_alg_linear :: "(('f \<times> 's list) \<times> 's)list \<Rightarrow> (('f \<times> 's list) \<times> 's)list \<Rightarrow> ('f,'v)term list \<Rightarrow> bool" where 
  "pat_complete_alg_linear C D lhss = (
  case decide_pat_complete_linear_lhss C D lhss of Inl err \<Rightarrow> Code.abort (err (STR '''')) (\<lambda> _. True)
    | Inr res \<Rightarrow> res)" 

definition pat_complete_alg_new :: "(('f \<times> 's list) \<times> 's)list \<Rightarrow> (('f \<times> 's list) \<times> 's)list \<Rightarrow> ('f,string)term list \<Rightarrow> bool" where 
  "pat_complete_alg_new C D lhss = (
  case decide_pat_complete_lhss_string C D lhss of Inl err \<Rightarrow> Code.abort (err (STR '''')) (\<lambda> _. True)
    | Inr res \<Rightarrow> res)" 


value (code) "pat_complete_alg_linear nat_bool even_nat even_lhss" (* return True *)
value (code) "pat_complete_alg_linear int_bool even_int even_lhss_int" (* return False *)

value (code) "pat_complete_alg_fscd nat_bool [((''f'',[''bool'',''bool'',''bool'']),''bool'')] non_lin_lhss" (* return True *)
value (code) "pat_complete_alg_fscd nat_bool [((''f'',[''nat'',''nat'',''nat'']),''bool'')] non_lin_lhss" (* return False *)


definition pat_complete_alg_test_linear :: "integer \<Rightarrow> integer \<Rightarrow> (integer list * integer list)list \<Rightarrow> bool" where
  "pat_complete_alg_test_linear c n perms = (case test_problem_integer c n perms of 
    (C,D,lhss) \<Rightarrow> pat_complete_alg_linear C D lhss)" 

definition pat_complete_alg_test_new :: "integer \<Rightarrow> integer \<Rightarrow> (integer list * integer list)list \<Rightarrow> bool" where
  "pat_complete_alg_test_new c n perms = (case test_problem_integer c n perms of 
    (C,D,lhss) \<Rightarrow> pat_complete_alg_new C D lhss)" 

definition test_problem_nl1 :: "integer \<Rightarrow> _" where
  "test_problem_nl1 n = (let 
    n' = int_of_integer n;
    s = (\<lambda> i. CHR ''s'' # show i);
    c = (\<lambda> i. ((CHR ''c'' # show i, if i = 0 then [] else [s (i - 1), s (i - 1)]), s i ));
    C = map c [0..n'];
    D = [((''f'', [s n', s n']), s 0)];
    lhss = [Fun ''f'' [Var ''x'', Var ''x'']]
  in (C, D, lhss))"

definition test_problem_nl2 :: "integer \<Rightarrow> _" where
  "test_problem_nl2 n = (case test_problem_nl1 n of
    (C, D, lhss) \<Rightarrow> (((''d'', []), ''s0'') # C, D, lhss))" 

definition test_problem_nl3 :: "integer \<Rightarrow> _" where
  "test_problem_nl3 n = (let 
    n' = int_of_integer (n + 1);
    s = (\<lambda> i. CHR ''s'' # show i);
    x = (\<lambda> i. Var (CHR ''x'' # show i));
    cSym = (\<lambda> i. CHR ''c'' # show i);
    c = (\<lambda> i. ((cSym i, if i = 0 then [] else [s (i - 1), s (i - 1)]), s i));
    C = map c [0..n'];
    D = [((''f'', map s [0..n']), s 0)];
    lhss = map (\<lambda> k. (Fun ''f'' (map (x(k + 1 := Fun (cSym (k + 1)) [x k, x k])) [0..n']))) [0..n' - 1]
  in (C, D, lhss))"

definition test_problem_nl4 :: "integer \<Rightarrow> _" where
  "test_problem_nl4 n = (case test_problem_nl3 n of
    (C, D, lhss) \<Rightarrow> (((''d'', []), ''s0'') # C, D, lhss))" 

definition test_pigeon_hole :: "int \<Rightarrow> nat \<Rightarrow> _" where
  "test_pigeon_hole n m = (let
     s = ''s'';
     f = ''f'';
     x = (\<lambda> i. Var (CHR ''x'' # show i));
     y = Var ''y'';
     C = map (\<lambda> i. (((CHR ''c'' # show i), [] :: string list), s)) [0 .. n];
     D = [((f, map (\<lambda> _. s) [0..<Suc m]), s)];
     xs = map x [0..<Suc m];
     l = (\<lambda> i j. xs [ i := y, j := y]); 
     lhss = List.maps (\<lambda> i. let xsi = xs [i := y] in
         map (\<lambda> j. Fun f (xsi[ j := y ])) [Suc i ..< Suc m]) [0..<m]
   in (C, D, lhss))" 

definition test_problem_nl5 :: "integer \<Rightarrow> _" where
  "test_problem_nl5 n = test_pigeon_hole (int_of_integer n) (nat_of_integer (n + 1))" 

definition test_problem_nl6 :: "integer \<Rightarrow> _" where
  "test_problem_nl6 n = test_pigeon_hole (int_of_integer (n + 1)) (nat_of_integer (n + 1))" 


definition test_problem_nl :: "integer \<Rightarrow> _" where
  "test_problem_nl c = (if c = 1 then test_problem_nl1
    else if c = 2 then test_problem_nl2
    else if c = 3 then test_problem_nl3
    else if c = 4 then test_problem_nl4
    else if c = 5 then test_problem_nl5
    else if c = 6 then test_problem_nl6
    else (\<lambda> _. ([],[],[])))"  

fun show_term :: "(string,string)term \<Rightarrow> showsl" where
  "show_term (Var x) = (+) (String.implode x)" 
| "show_term (Fun f []) = (+) (String.implode f)" 
| "show_term (Fun f ts) = showsl_paren (\<lambda> s. String.implode f + STR '' '' + 
    showsl_sep id ((+) STR '' '') (map show_term ts) s)" 


definition show_pat_complete_test_nl :: "integer \<Rightarrow> integer \<Rightarrow> String.literal" where
  "show_pat_complete_test_nl c n = (case test_problem_nl c n of 
    (C,D,lhss) \<Rightarrow> let sorts = remdups (map snd C);
      baseS = snd (hd D);
      baseC = (fst o fst o hd o filter (\<lambda> ((_,ss),s). ss = [] \<and> s = baseS)) C;
      tos = String.implode;
      s_sym = (\<lambda> ((f,ss),s). STR ''(fun '' + tos f + STR '' '' + 
       (if ss = [] then tos s else STR ''(-> '' + showsl_sep ((+) o tos) ((+) STR '' '') (ss @ [s]) (STR '')''))
        + STR '')'');
      rule = (\<lambda> l. let sl = show_term l (STR '''') in STR ''(rule '' + sl + STR '' '' + tos baseC + STR '')'')
 
     in showsl_sep (+) showsl_nl 
      ([STR ''(format MSTRS)''] @
      map (\<lambda> s. STR ''(sort '' + tos s + STR '')'') sorts @
      map s_sym C @ map s_sym D @
      map rule lhss
      )
     ) (STR '''')" 

value (code) "show_pat_complete_test_nl 1 3" 

definition pat_complete_alg_test_nl_new :: "integer \<Rightarrow> integer  \<Rightarrow> bool" where
  "pat_complete_alg_test_nl_new c n = (case test_problem_nl c n of 
    (C,D,lhss) \<Rightarrow> pat_complete_alg_new C D lhss)" 

definition pat_complete_alg_test_nl_fscd :: "integer \<Rightarrow> integer  \<Rightarrow> bool" where
  "pat_complete_alg_test_nl_fscd c n = (case test_problem_nl c n of 
    (C,D,lhss) \<Rightarrow> pat_complete_alg_fscd C D lhss)" 

value(code) "showsl (test_problem_nl1 2) (STR '''')" 
lemma "pat_complete_alg_test_nl_new 1 2" by eval

value(code) "showsl (test_problem_nl2 2) (STR '''')"
lemma "\<not> pat_complete_alg_test_nl_new 2 2" by eval

value(code) "showsl (test_problem_nl3 2) (STR '''')" 
lemma "pat_complete_alg_test_nl_new 3 2" by eval

value(code) "showsl (test_problem_nl4 2) (STR '''')"
lemma "\<not> pat_complete_alg_test_nl_new 4 2" by eval

value(code) "showsl (test_problem_nl5 2) (STR '''')" 
lemma "pat_complete_alg_test_nl_new 5 2" by eval

value(code) "showsl (test_problem_nl6 2) (STR '''')"
lemma "\<not> pat_complete_alg_test_nl_new 6 2" by eval

declare [[code drop: "equal_class.equal :: bool \<Rightarrow> bool \<Rightarrow> bool"]]

(* TODO: omit these code equation setup, once it has been fixed *)
lemma equal_bool_code[code]:  
  "equal_class.equal p False = (\<not> p)" 
  "equal_class.equal p True = p"
  unfolding equal_eq by auto
(* END TODO *)

subsection \<open>Export Code to SML and Haskell\<close>

text \<open>Connection to AGCP, which is written in SML, and 
  SML-export of verified pattern completeness algorithms\<close>

export_code
  pat_complete_alg_test_fscd
  pat_complete_alg_test_linear
  pat_complete_alg_test_new
  pat_complete_alg_test_nl_new
  pat_complete_alg_test_nl_fscd
  show_pat_complete_test 
  create_agcp_input
  pat_complete_alg_fscd
  strong_quasi_reducible_alg
  Var
  in SML module_name Pat_Complete 
  (* locally stored in file "../experiments/SML/src-agcp-v0.02/src/pat_complete_tests/pat_complete.sml" *)


text \<open>Connection to FORT, which is written in Haskell, and 
  Haskell-export of verified pattern completeness algorithms\<close>

export_code encodeAutomata 
  showAutomata
  patCompleteAutomataTest
  show_pat_complete_test
  show_pat_complete_test_nl
  pat_complete_alg_test_fscd
  pat_complete_alg_test_linear
  pat_complete_alg_test_new
  pat_complete_alg_test_nl_new
  pat_complete_alg_test_nl_fscd
  createHaskellInput
  in Haskell module_name Pat_Test_Generated 
  (* locally stored in file "../experiments/Haskell/pat-complete-0.1.0.0" *)


end