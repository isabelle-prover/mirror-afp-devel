section \<open>Setup for Experiments\<close>

theory Test_Pat_Complete
  imports 
    Pattern_Completeness
    "HOL-Library.Code_Abstract_Char"
    "HOL-Library.Code_Target_Numeral"
begin

text \<open>turn error message into runtime error\<close>
definition pat_complete_alg :: "(('f \<times> 's list) \<times> 's)list \<Rightarrow> (('f \<times> 's list) \<times> 's)list \<Rightarrow> ('f,'v)term list \<Rightarrow> bool" where 
  "pat_complete_alg C D lhss = (
  case decide_pat_complete_lhss C D lhss of Inl err \<Rightarrow> Code.abort (err (STR '''')) (\<lambda> _. True)
    | Inr res \<Rightarrow> res)" 

text \<open>turn error message into runtime error\<close>
definition strong_quasi_reducible_alg :: "(('f \<times> 's list) \<times> 's)list \<Rightarrow> (('f \<times> 's list) \<times> 's)list \<Rightarrow> ('f,'v)term list \<Rightarrow> bool" where 
  "strong_quasi_reducible_alg C D lhss = (
  case decide_strong_quasi_reducible C D lhss of Inl err \<Rightarrow> Code.abort (err (STR '''')) (\<lambda> _. True)
    | Inr res \<Rightarrow> res)" 

text \<open>Examples\<close>
definition "nat_bool = [ 
   ((''zero'', []), ''nat''),
   ((''succ'', [''nat'']), ''nat''),
   ((''true'', []), ''bool''),
   ((''false'', []), ''bool'')
   ]"

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

lemma decide_pat_complete_wrapper: 
  assumes "(case decide_pat_complete_lhss C D lhss of Inr b \<Rightarrow> Some b | Inl _ \<Rightarrow> None) = Some res"
  shows "pat_complete_lhss (map_of C) (map_of D) (set lhss) = res" 
  using decide_pat_complete_lhss[of C D lhss] assms by (auto split: sum.splits)

lemma decide_strong_quasi_reducible_wrapper: 
  assumes "(case decide_strong_quasi_reducible C D lhss of Inr b \<Rightarrow> Some b | Inl _ \<Rightarrow> None) = Some res"
  shows "strong_quasi_reducible (map_of C) (map_of D) (set lhss) = res" 
  using decide_strong_quasi_reducible[of C D lhss] assms by (auto split: sum.splits)

lemma "pat_complete_lhss (map_of nat_bool) (map_of even_nat) (set even_lhss)"
  apply (subst decide_pat_complete_wrapper[of _ _ _ True])
  by eval+

lemma "\<not> pat_complete_lhss (map_of int_bool) (map_of even_int) (set even_lhss_int)" 
  apply (subst decide_pat_complete_wrapper[of _ _ _ False])
  by eval+


lemma "strong_quasi_reducible (map_of int_bool) (map_of even_int) (set even_lhss_int)" 
  apply (subst decide_strong_quasi_reducible_wrapper[of _ _ _ True])
  by eval+

definition "non_lin_lhss = [
  Fun ''f'' [Var ''x'', Var ''x'', Var ''y''],
  Fun ''f'' [Var ''x'', Var ''y'', Var ''x''],
  Fun ''f'' [Var ''y'', Var ''x'', Var ''x'']
  ]"

lemma "pat_complete_lhss (map_of nat_bool) (map_of [((''f'',[''bool'',''bool'',''bool'']),''bool'')]) (set non_lin_lhss)" 
  apply (subst decide_pat_complete_wrapper[of _ _ _ True])
  by eval+

lemma "\<not> pat_complete_lhss (map_of nat_bool) (map_of [((''f'',[''nat'',''nat'',''nat'']),''bool'')]) (set non_lin_lhss)" 
  apply (subst decide_pat_complete_wrapper[of _ _ _ False])
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

definition pat_complete_alg_test :: "integer \<Rightarrow> integer \<Rightarrow> (integer list * integer list)list \<Rightarrow> bool" where
  "pat_complete_alg_test c n perms = (case test_problem_integer c n perms of 
    (C,D,lhss) \<Rightarrow> pat_complete_alg C D lhss)" 

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

text \<open>connection to AGCP, which is written in SML, and 
  SML-export of verified pattern completeness algorithm\<close>
export_code 
  pat_complete_alg_test 
  show_pat_complete_test 
  create_agcp_input
  pat_complete_alg
  strong_quasi_reducible_alg
  Var
  in SML module_name Pat_Complete


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

definition string_append :: "String.literal \<Rightarrow> String.literal \<Rightarrow> String.literal" (infixr "+++" 65) where
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

text \<open>connection to FORT-h, generation of Haskell-examples, and Haskell tests of 
  verified pattern completeness algorithm\<close>
export_code encodeAutomata 
  showAutomata
  patCompleteAutomataTest
  show_pat_complete_test
  pat_complete_alg_test
  createHaskellInput
  in Haskell module_name Pat_Test_Generated 

end