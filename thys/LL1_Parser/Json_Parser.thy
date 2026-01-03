subsection \<open>Generating a JSON Parser\<close>

theory Json_Parser
  imports LL1_Parser_show "Show.Show_Instances" "HOL-Library.Code_Target_Numeral"
begin

datatype terminal =
    TNum
  | Str
  | Tru
  | Fls
  | Null
  | LeftBrace
  | RightBrace
  | LeftBrack
  | RightBrack
  | Colon
  | Comma

datatype nterminal =
    Value
  | Pairs
  | PairsTl
  | Pair
  | Elts
  | EltsTl

derive "show" "terminal"
derive "show" "nterminal"
derive "show" "(terminal, nterminal) symbol"

definition jsonGrammar :: "(nterminal, terminal) grammar" where
  "jsonGrammar = G Value [
    (Value, [T LeftBrace, NT Pairs, T RightBrace]),
    (Value, [T LeftBrack, NT Elts, T RightBrack]),
    (Value, [T Str]),
    (Value, [T TNum]),
    (Value, [T Tru]),
    (Value, [T Fls]),
    (Value, [T Null]),

    (Pairs, []),
    (Pairs, [NT Pair, NT PairsTl]),

    (PairsTl, []),
    (PairsTl, [T Comma, NT Pair, NT PairsTl]),

    (Pair, [T Str, T Colon, NT Value]),

    (Elts, []),
    (Elts, [NT Value, NT EltsTl]),

    (EltsTl, []),
    (EltsTl, [T Comma, NT Value, NT EltsTl])
  ]"

definition pt :: "(nterminal, terminal) ll1_parse_table" where
  "pt = mkParseTable jsonGrammar"

datatype json_number =
  JsonNumber
    (neg: bool)
    (int:  nat)
    (frac: "string option") \<comment> \<open>string due to leading zeros\<close>
    (exp_neg: bool)
    (exp: "nat option")

hide_const (open)
  json_number.neg json_number.int json_number.frac json_number.exp_neg json_number.exp

datatype lex =
    LNum (lex_num: json_number)
  | LStr (lex_str: string)
  | LNone

derive "show" "json_number"
derive "show" "lex"

definition
  "mkS x = (x, LNone)"

definition
  "StrS s = (Str, LStr s)"

abbreviation
  "LeftBraceS \<equiv> mkS LeftBrace"

abbreviation
  "RightBraceS \<equiv> mkS RightBrace"

abbreviation
  "LeftBrackS \<equiv> mkS LeftBrack"

abbreviation
  "RightBrackS \<equiv> mkS RightBrack"

abbreviation
  "ColonS \<equiv> mkS Colon"

abbreviation
  "CommaS \<equiv> mkS Comma"

abbreviation
  "FlsS \<equiv> mkS Fls"

abbreviation
  "TruS \<equiv> mkS Tru"

definition
  "IntS n = (TNum, LNum (JsonNumber False n None False None))"

text\<open>Example input:
\<^verbatim>\<open>{
  "items": []
}\<close>
\<close>

lemma "parse pt (NT (start jsonGrammar))
  [LeftBraceS, StrS ''items'', ColonS, LeftBrackS, RightBrackS, RightBraceS] =
  RESULT
   (Node Value
       [Leaf (mkS LeftBrace),
        Node Pairs [
          Node Pair [Leaf (StrS ''items''), Leaf (mkS Colon),
            Node Value [Leaf (mkS LeftBrack), Node Elts [], Leaf (mkS RightBrack)]],
          Node PairsTl []],
        Leaf (mkS RightBrace)])
   [] True"
  by eval

text\<open>Example input:
\<^verbatim>\<open>{
  "items": [
    {
    "id":           65,
    "description":  "Title",
    "visible":      false},
    {
    "id":           42,
    "visible":      true}
  ]
}\<close>
\<close>

lemma "parse pt (NT (start jsonGrammar))
  [LeftBraceS, StrS ''items'', ColonS, LeftBrackS,
    LeftBraceS, StrS ''id'', ColonS, IntS 65, CommaS, StrS ''description'', ColonS, StrS ''Title'',
    CommaS, StrS ''visible'', ColonS, FlsS, RightBraceS, CommaS,
    LeftBraceS, StrS ''id'', ColonS, IntS 42, CommaS, StrS ''visible'', ColonS, TruS,
    RightBraceS, RightBrackS, RightBraceS] =
  RESULT
   (Node Value
       [Leaf LeftBraceS,
        Node Pairs [
          Node Pair [Leaf (StrS ''items''), Leaf ColonS,
            Node Value
             [Leaf LeftBrackS,
              Node Elts
               [Node Value
                 [Leaf LeftBraceS,
                  Node Pairs
                   [Node Pair [Leaf (StrS ''id''), Leaf ColonS, Node Value [Leaf (IntS 65)]],
                    Node PairsTl [Leaf CommaS,
                      Node Pair [
                        Leaf (StrS ''description''), Leaf ColonS, Node Value [Leaf (StrS ''Title'')]
                      ],
                      Node PairsTl [Leaf CommaS,
                      Node Pair [
                        Leaf (StrS ''visible''), Leaf ColonS,
                        Node Value [Leaf FlsS]], Node PairsTl []
                      ]]],
                  Leaf RightBraceS],
                Node EltsTl
                 [Leaf CommaS,
                  Node Value
                   [Leaf LeftBraceS,
                    Node Pairs
                     [Node Pair [Leaf (StrS ''id''), Leaf ColonS, Node Value [Leaf (IntS 42)]],
                      Node PairsTl [Leaf CommaS,
                      Node Pair [Leaf (StrS ''visible''), Leaf ColonS, Node Value [Leaf TruS]],
                      Node PairsTl []]],
                    Leaf RightBraceS],
                  Node EltsTl []]],
              Leaf RightBrackS]],
          Node PairsTl []],
        Leaf RightBraceS])
   [] True"
  by eval

subsection \<open>Reading the Parse Tree\<close>

\<comment> \<open>A datatype for JSON\<close>
datatype JSON =
  Object "(string \<times> JSON) list"
| Array "JSON list"
| String string \<comment>\<open>An Isabelle string rather than a JSON string\<close>
| Num json_number
| Boolean bool \<comment>\<open>True and False are contracted to one constructor\<close>
| Nil

primrec fold_parse_tree :: "('t \<Rightarrow> 'a) \<Rightarrow> ('a list \<Rightarrow> 'n \<Rightarrow> 'a) \<Rightarrow> ('n, 't) parse_tree \<Rightarrow> 'a"
where
  "fold_parse_tree t n (Leaf x) = t x"
| "fold_parse_tree t n (Node x ts) = n (map (fold_parse_tree t n) ts) x"

definition
  "json_leaf \<equiv> \<lambda>(t, s). (case t of
    Str => JSON.String (lex_str s) |
    TNum => JSON.Num (lex_num s) |
    Tru \<Rightarrow> JSON.Boolean True |
    Fls => JSON.Boolean False |
    Null => JSON.Nil |
    _ \<Rightarrow> JSON.Nil
)"

definition
  "combine_objects x y = (case x of JSON.Object xs \<Rightarrow> case y of JSON.Object ys \<Rightarrow>
    JSON.Object (xs @ ys)
  )"

definition
  "cons_array x y = (case y of JSON.Array ys \<Rightarrow>
    JSON.Array (x # ys)
  )"

definition
  "the_str = (\<lambda>JSON.String s \<Rightarrow> s)"

definition
  "json_node vs = (
  \<lambda> Value \<Rightarrow> (
    case vs of
      [x] \<Rightarrow> x
    | [x,y,z] \<Rightarrow> y
  )
  | Pair \<Rightarrow> (
    case vs of
      [s, _, v] \<Rightarrow> JSON.Object [(the_str s, v)]
  )
  | Pairs \<Rightarrow> (
    case vs of
      [] \<Rightarrow> JSON.Object []
    | [n,ntl] \<Rightarrow> combine_objects n ntl
  )
  | PairsTl \<Rightarrow> (
    case vs of
      [] \<Rightarrow> JSON.Object []
    | [_,n,ntl] \<Rightarrow> combine_objects n ntl
  )
  | Elts \<Rightarrow> (
    case vs of
      [] \<Rightarrow> JSON.Array []
    | [n,ntl] \<Rightarrow> cons_array n ntl
  )
  | EltsTl \<Rightarrow> (
    case vs of
      [] \<Rightarrow> JSON.Array []
    | [_,n,ntl] \<Rightarrow> cons_array n ntl
  )
)"

definition
  "parse_tree_to_json = fold_parse_tree json_leaf json_node"

definition
  "the_RESULT = (\<lambda>RESULT r _ _ \<Rightarrow> r)"

lemma "parse_tree_to_json (the_RESULT (parse pt (NT (start jsonGrammar))
  [LeftBraceS, StrS ''items'', ColonS, LeftBrackS, RightBrackS, RightBraceS]))
= Object [(''items'', Array [])]"
  by eval

lemma "parse_tree_to_json (the_RESULT (parse pt (NT (start jsonGrammar))
  [LeftBraceS, StrS ''items'', ColonS, LeftBrackS,
    LeftBraceS, StrS ''id'', ColonS, IntS 65, CommaS, StrS ''description'', ColonS, StrS ''Title'',
    CommaS, StrS ''visible'', ColonS, FlsS, RightBraceS, CommaS,
    LeftBraceS, StrS ''id'', ColonS, IntS 42, CommaS, StrS ''visible'', ColonS, TruS,
    RightBraceS, RightBrackS, RightBraceS]))
= Object
    [(''items'',
      Array
       [Object
         [(''id'', JSON.Num (JsonNumber False 65 None False None)),
          (''description'', String ''Title''),
          (''visible'', Boolean False)],
        Object
          [(''id'', JSON.Num (JsonNumber False 42 None False None)),
           (''visible'', Boolean True)]])]"
  by eval

text \<open>
Note that in Vermillion one can attach the functions to read parse trees directly
to the production rules.
While this would be possible in Isabelle/HOL, it would give little advantage over defining
the reader function directly, since we are missing dependent types.
\<close>

subsection \<open>JSON Lexing as LL1 Parsing\<close>

definition
  "is_digit x \<equiv> x \<in> {
    CHR ''0'', CHR ''1'', CHR ''2'', CHR ''3'', CHR ''4'', CHR ''5'', CHR ''6'', CHR ''7'',
    CHR ''8'', CHR ''9''}"

definition is_hex :: "char \<Rightarrow> bool" where
  "is_hex c \<equiv>
   let n = of_char c :: nat in
     is_digit c \<or>
     (of_char (CHR ''A'') \<le> n \<and> n \<le> of_char (CHR ''F'')) \<or>
     (of_char (CHR ''a'') \<le> n \<and> n \<le> of_char (CHR ''f''))"

datatype chr =
    COneNine | CZero
  | CMinus | CPlus | CDot | CE | Ce
  | CSpace | CWS
  | CQuote | CBackslash | CSlash
  | Ct | Cr | Cu
  | Cf | Ca | Cl | Cs
  | Cn | Cb
  | CLBrace | CRBrace | CLBrack | CRBrack
  | CColon | CComma
  | CStringChar | CControlChar
  | CHex

datatype lterminal = LRoot | LStartStr | LEscape
  | LStartInt | LZero | LMinus | LStartFrac | LFrac | LExp | LStartExp | LExpSign
  | LUnicode1 | LUnicode2 | LUnicode3 | LUnicode4

definition jsonLex :: "(lterminal + terminal, chr) grammar" where
  "jsonLex = G (Inl LRoot) [

  \<comment>\<open> whitespace \<close>
  (Inl LRoot, []),
  (Inl LRoot, [T CWS, NT (Inl LRoot)]),
  (Inl LRoot, [T CSpace, NT (Inl LRoot)]),

  \<comment>\<open> punctuation \<close>
  (Inl LRoot, [T CLBrace, NT (Inr LeftBrace), NT (Inl LRoot)]),
  (Inl LRoot, [T CRBrace, NT (Inr RightBrace), NT (Inl LRoot)]),
  (Inl LRoot, [T CLBrack, NT (Inr LeftBrack), NT (Inl LRoot)]),
  (Inl LRoot, [T CRBrack, NT (Inr RightBrack), NT (Inl LRoot)]),
  (Inl LRoot, [T CColon,  NT (Inr Colon), NT (Inl LRoot)]),
  (Inl LRoot, [T CComma,  NT (Inr Comma), NT (Inl LRoot)]),
  (Inr LeftBrace, []),
  (Inr RightBrace, []),
  (Inr LeftBrack, []),
  (Inr RightBrack, []),
  (Inr Colon, []),
  (Inr Comma, []),

  \<comment>\<open> true  \<close>
  (Inl LRoot, [T Ct, T Cr, T Cu, T Ce, NT (Inr Tru), NT (Inl LRoot)]),
  (Inr Tru, []),

  \<comment>\<open> false \<close>
  (Inl LRoot, [T Cf, T Ca, T Cl, T Cs, T Ce, NT (Inr Fls), NT (Inl LRoot)]),
  (Inr Fls, []),

  \<comment>\<open> null \<close>
  (Inl LRoot, [T Cn, T Cu, T Cl, T Cl, NT (Inr Null), NT (Inl LRoot)]),
  (Inr Null, []),

  \<comment>\<open> ---------- string ---------- \<close>
  (Inl LRoot, [T CQuote, NT (Inl LStartStr), NT (Inl LRoot)]),

  \<comment>\<open> unescaped characters allowed inside strings \<close>
  (Inl LStartStr,   [T CStringChar,  NT (Inr Str)]),
  (Inl LStartStr,   [T CHex,         NT (Inr Str)]),
  (Inl LStartStr,   [T CZero,        NT (Inr Str)]),
  (Inl LStartStr,   [T COneNine,     NT (Inr Str)]),
  (Inl LStartStr,   [T CMinus,       NT (Inr Str)]),
  (Inl LStartStr,   [T CPlus,        NT (Inr Str)]),
  (Inl LStartStr,   [T CDot,         NT (Inr Str)]),
  (Inl LStartStr,   [T CE,           NT (Inr Str)]),
  (Inl LStartStr,   [T Ce,           NT (Inr Str)]),
  (Inl LStartStr,   [T CSlash,       NT (Inr Str)]),
  
  (Inl LStartStr,   [T Ct, NT (Inr Str)]),
  (Inl LStartStr,   [T Cr, NT (Inr Str)]),
  (Inl LStartStr,   [T Cu, NT (Inr Str)]),
  (Inl LStartStr,   [T Cf, NT (Inr Str)]),
  (Inl LStartStr,   [T Ca, NT (Inr Str)]),
  (Inl LStartStr,   [T Cl, NT (Inr Str)]),
  (Inl LStartStr,   [T Cs, NT (Inr Str)]),
  (Inl LStartStr,   [T Cn, NT (Inr Str)]),
  (Inl LStartStr,   [T Cb, NT (Inr Str)]),
  
  (Inl LStartStr,   [T CLBrace,  NT (Inr Str)]),
  (Inl LStartStr,   [T CRBrace,  NT (Inr Str)]),
  (Inl LStartStr,   [T CLBrack,  NT (Inr Str)]),
  (Inl LStartStr,   [T CRBrack,  NT (Inr Str)]),
  (Inl LStartStr,   [T CColon,   NT (Inr Str)]),
  (Inl LStartStr,   [T CComma,   NT (Inr Str)]),
  (Inl LStartStr,   [T CSpace,      NT (Inr Str)]),
  
  (Inr Str,   [T CStringChar,  NT (Inr Str)]),
  (Inr Str,   [T CHex,         NT (Inr Str)]),
  (Inr Str,   [T CZero,        NT (Inr Str)]),
  (Inr Str,   [T COneNine,     NT (Inr Str)]),
  (Inr Str,   [T CMinus,       NT (Inr Str)]),
  (Inr Str,   [T CPlus,        NT (Inr Str)]),
  (Inr Str,   [T CDot,         NT (Inr Str)]),
  (Inr Str,   [T CE,           NT (Inr Str)]),
  (Inr Str,   [T Ce,           NT (Inr Str)]),
  (Inr Str,   [T CSlash,       NT (Inr Str)]),
  
  (Inr Str,   [T Ct, NT (Inr Str)]),
  (Inr Str,   [T Cr, NT (Inr Str)]),
  (Inr Str,   [T Cu, NT (Inr Str)]),
  (Inr Str,   [T Cf, NT (Inr Str)]),
  (Inr Str,   [T Ca, NT (Inr Str)]),
  (Inr Str,   [T Cl, NT (Inr Str)]),
  (Inr Str,   [T Cs, NT (Inr Str)]),
  (Inr Str,   [T Cn, NT (Inr Str)]),
  (Inr Str,   [T Cb, NT (Inr Str)]),
  
  (Inr Str,   [T CLBrace,  NT (Inr Str)]),
  (Inr Str,   [T CRBrace,  NT (Inr Str)]),
  (Inr Str,   [T CLBrack,  NT (Inr Str)]),
  (Inr Str,   [T CRBrack,  NT (Inr Str)]),
  (Inr Str,   [T CColon,   NT (Inr Str)]),
  (Inr Str,   [T CComma,   NT (Inr Str)]),
  (Inr Str,   [T CSpace,      NT (Inr Str)]),
  
  \<comment>\<open> escape sequence introducer \<close>
  (Inr Str,       [T CBackslash, NT (Inl LEscape), NT (Inr Str)]),
  (Inl LStartStr, [T CBackslash, NT (Inl LEscape), NT (Inr Str)]),
  (Inl LEscape,   [T CQuote]),
  (Inl LEscape,   [T CBackslash]),
  (Inl LEscape,   [T CSlash]),
  (Inl LEscape,   [T Cb]),
  (Inl LEscape,   [T Cf]),
  (Inl LEscape,   [T Cn]),
  (Inl LEscape,   [T Cr]),
  (Inl LEscape,   [T Ct]),

  \<comment>\<open> unicode code points \<close>
  (Inl LEscape,   [T Cu, NT (Inl LUnicode1)]),

  (Inl LUnicode1, [T CZero,    NT (Inl LUnicode2)]),
  (Inl LUnicode1, [T COneNine, NT (Inl LUnicode2)]),
  (Inl LUnicode1, [T CHex,     NT (Inl LUnicode2)]),
  (Inl LUnicode1, [T Ca,       NT (Inl LUnicode2)]),
  (Inl LUnicode1, [T Cb,       NT (Inl LUnicode2)]),
  (Inl LUnicode1, [T Ce,       NT (Inl LUnicode2)]),
  (Inl LUnicode1, [T CE,       NT (Inl LUnicode2)]),
  (Inl LUnicode1, [T Cf,       NT (Inl LUnicode2)]),

  (Inl LUnicode2, [T CZero,    NT (Inl LUnicode3)]),
  (Inl LUnicode2, [T COneNine, NT (Inl LUnicode3)]),
  (Inl LUnicode2, [T CHex,     NT (Inl LUnicode3)]),
  (Inl LUnicode2, [T Ca,       NT (Inl LUnicode3)]),
  (Inl LUnicode2, [T Cb,       NT (Inl LUnicode3)]),
  (Inl LUnicode2, [T Ce,       NT (Inl LUnicode3)]),
  (Inl LUnicode2, [T CE,       NT (Inl LUnicode3)]),
  (Inl LUnicode2, [T Cf,       NT (Inl LUnicode3)]),

  (Inl LUnicode3, [T CZero,    NT (Inl LUnicode4)]),
  (Inl LUnicode3, [T COneNine, NT (Inl LUnicode4)]),
  (Inl LUnicode3, [T CHex,     NT (Inl LUnicode4)]),
  (Inl LUnicode3, [T Ca,       NT (Inl LUnicode4)]),
  (Inl LUnicode3, [T Cb,       NT (Inl LUnicode4)]),
  (Inl LUnicode3, [T Ce,       NT (Inl LUnicode4)]),
  (Inl LUnicode3, [T CE,       NT (Inl LUnicode4)]),
  (Inl LUnicode3, [T Cf,       NT (Inl LUnicode4)]),

  (Inl LUnicode4, [T CZero]),
  (Inl LUnicode4, [T COneNine]),
  (Inl LUnicode4, [T CHex]),
  (Inl LUnicode4, [T Ca]),
  (Inl LUnicode4, [T Cb]),
  (Inl LUnicode4, [T Ce]),
  (Inl LUnicode4, [T CE]),
  (Inl LUnicode4, [T Cf]),

  \<comment>\<open> closing quote \<close>
  (Inl LStartStr, [T CQuote]),
  (Inr Str,       [T CQuote]),

  \<comment>\<open> integer \<close>
  (Inl LRoot, [T CZero, NT (Inl LZero)]),
  (Inl LRoot, [T CMinus, NT (Inl LMinus)]),
  (Inl LRoot, [T COneNine, NT (Inl LStartInt)]),

  (Inl LMinus, [T CZero, NT (Inl LZero)]),
  (Inl LMinus, [T COneNine, NT (Inl LStartInt)]),

  (Inl LZero, [T CDot, NT (Inl LStartFrac)]),
  (Inl LZero, [T CComma, NT (Inr Comma), NT (Inl LRoot)]),
  (Inl LZero, [T CRBrack, NT (Inr RightBrack), NT (Inl LRoot)]),
  (Inl LZero, [T CRBrace, NT (Inr RightBrace), NT (Inl LRoot)]),
  (Inl LZero, [T CWS, NT (Inl LRoot)]),
  (Inl LZero, [T CSpace, NT (Inl LRoot)]),
  (Inl LZero, []),

  (Inl LStartInt, [T CZero, NT (Inr TNum)]),
  (Inl LStartInt, [T COneNine, NT (Inr TNum)]),
  (Inl LStartInt, [T CDot, NT (Inl LStartFrac)]),
  (Inl LStartInt, [T CComma, NT (Inr Comma), NT (Inl LRoot)]),
  (Inl LStartInt, [T CRBrack, NT (Inr RightBrack), NT (Inl LRoot)]),
  (Inl LStartInt, [T CRBrace, NT (Inr RightBrace), NT (Inl LRoot)]),
  (Inl LStartInt, [T CWS, NT (Inl LRoot)]),
  (Inl LStartInt, [T CSpace, NT (Inl LRoot)]),
  (Inl LStartInt, []),

  (Inr TNum, [T CZero, NT (Inr TNum)]),
  (Inr TNum, [T COneNine, NT (Inr TNum)]),
  (Inr TNum, [T CComma, NT (Inr Comma), NT (Inl LRoot)]),
  (Inr TNum, [T CRBrack, NT (Inr RightBrack), NT (Inl LRoot)]),
  (Inr TNum, [T CRBrace, NT (Inr RightBrace), NT (Inl LRoot)]),
  (Inr TNum, [T CWS, NT (Inl LRoot)]),
  (Inr TNum, [T CSpace, NT (Inl LRoot)]),
  (Inr TNum, []),

  \<comment>\<open> fraction \<close>
  (Inr TNum, [T CDot, NT (Inl LStartFrac)]),

  (Inl LStartFrac, [T CZero,    NT (Inl LFrac)]),
  (Inl LStartFrac, [T COneNine, NT (Inl LFrac)]),

  (Inl LFrac, [T CZero, NT (Inl LFrac)]),
  (Inl LFrac, [T COneNine, NT (Inl LFrac)]),
  (Inl LFrac, [T CComma, NT (Inr Comma), NT (Inl LRoot)]),
  (Inl LFrac, [T CRBrack, NT (Inr RightBrack), NT (Inl LRoot)]),
  (Inl LFrac, [T CRBrace, NT (Inr RightBrace), NT (Inl LRoot)]),
  (Inl LFrac, [T CWS, NT (Inl LRoot)]),
  (Inl LFrac, [T CSpace, NT (Inl LRoot)]),
  (Inl LFrac, []),

  \<comment>\<open> exponent \<close>
  (Inl LZero,     [T CE, NT (Inl LStartExp)]),
  (Inl LZero,     [T Ce, NT (Inl LStartExp)]),
  (Inr TNum,      [T CE, NT (Inl LStartExp)]),
  (Inr TNum,      [T Ce, NT (Inl LStartExp)]),
  (Inl LStartInt, [T CE, NT (Inl LStartExp)]),
  (Inl LStartInt, [T Ce, NT (Inl LStartExp)]),
  (Inl LFrac,     [T CE, NT (Inl LStartExp)]),
  (Inl LFrac,     [T Ce, NT (Inl LStartExp)]),

  (Inl LStartExp, [T CPlus,    NT (Inl LExpSign)]),
  (Inl LStartExp, [T CMinus,   NT (Inl LExpSign)]),
  (Inl LStartExp, [T CZero,    NT (Inl LExp)]),
  (Inl LStartExp, [T COneNine, NT (Inl LExp)]),

  (Inl LExpSign, [T CZero,    NT (Inl LExp)]),
  (Inl LExpSign, [T COneNine, NT (Inl LExp)]),

  (Inl LExp, [T CZero,    NT (Inl LExp)]),
  (Inl LExp, [T COneNine, NT (Inl LExp)]),
  (Inl LExp, [T CComma,   NT (Inr Comma),      NT (Inl LRoot)]),
  (Inl LExp, [T CRBrack,  NT (Inr RightBrack), NT (Inl LRoot)]),
  (Inl LExp, [T CRBrace,  NT (Inr RightBrace), NT (Inl LRoot)]),
  (Inl LExp, [T CWS,      NT (Inl LRoot)]),
  (Inl LExp, [T CSpace,   NT (Inl LRoot)]),
  (Inl LExp, [])
]"

definition lex_pt :: "(lterminal + terminal, chr) ll1_parse_table" where
  "lex_pt = mkParseTable jsonLex"

\<comment> \<open>The parse table is valid.\<close>
lemma "case lex_pt of ERROR_GRAMMAR_NOT_LL1_AMB_LA _ \<Rightarrow> False | _ \<Rightarrow> True"
  by eval

definition is_ws :: "char \<Rightarrow> bool" where
  "is_ws c \<equiv> c = CHR '' '' \<or> c = CHR ''\<newline>'' \<or> c = CHR 0x0D \<or> c = CHR 0x09"

definition is_control :: "char \<Rightarrow> bool" where
  "is_control c \<equiv> of_char c < (32::nat)"

definition char_to_chr :: "char \<Rightarrow> chr" where
  "char_to_chr c =
    (if c = CHR ''{'' then CLBrace else
     if c = CHR ''}'' then CRBrace else
     if c = CHR ''['' then CLBrack else
     if c = CHR '']'' then CRBrack else
     if c = CHR '':'' then CColon else
     if c = CHR '','' then CComma else

     if c = CHR ''\"'' then CQuote else
     if c = CHR 0x5C   then CBackslash else
     if c = CHR ''/''  then CSlash else

     if c = CHR ''0'' then CZero else
     if is_digit c then COneNine else

     if c = CHR ''-'' then CMinus else
     if c = CHR ''+'' then CPlus else
     if c = CHR ''.'' then CDot else
     if c = CHR ''E'' then CE else
     if c = CHR ''e'' then Ce else

     if c = CHR ''t'' then Ct else
     if c = CHR ''r'' then Cr else
     if c = CHR ''u'' then Cu else
     if c = CHR ''f'' then Cf else
     if c = CHR ''a'' then Ca else
     if c = CHR ''l'' then Cl else
     if c = CHR ''s'' then Cs else
     if c = CHR ''n'' then Cn else
     if c = CHR ''b'' then Cb else

     if c = CHR '' '' then CSpace else
     if is_ws c then CWS else
     if is_control c then CControlChar else
     if is_hex c then CHex else
     CStringChar)"

definition
  "mk_chrs = map (\<lambda>x. (char_to_chr x, x))"

derive "show" "chr"

definition lex_leaf ::
  "(chr \<times> char) \<Rightarrow> (char + terminal \<times> lex) list" where
  "lex_leaf = (\<lambda>(t, c). [Inl c])"

definition string_to_nat :: "string \<Rightarrow> nat" where
  "string_to_nat s = horner_sum (\<lambda>c. of_char c - of_char (CHR ''0'')) 10 (rev s)"

definition
  "is_1_9 c \<equiv> of_char (CHR ''0'') < (of_char c :: nat) \<and> (of_char c :: nat) \<le> of_char (CHR ''9'')"

definition
  "ends_int c \<equiv> c \<in> {CHR '','', CHR ''}'', CHR '']''} \<or> is_ws c"

definition combine_strings where
  "combine_strings xs \<equiv> let
      ys = concat xs;
      as = takeWhile (\<lambda>Inl c \<Rightarrow> \<not> ends_int c | Inr (Str, LStr s) \<Rightarrow> True | _ \<Rightarrow> False) ys;
      s  = List.maps (\<lambda>Inl c \<Rightarrow> [c] | Inr (Str, LStr s) \<Rightarrow> s    | _ \<Rightarrow> '''') as;
      bs = dropWhile (\<lambda>Inl c \<Rightarrow> \<not> ends_int c | Inr (Str, LStr s) \<Rightarrow> True | _ \<Rightarrow> False) ys
  in (s, bs)"

definition map_escape :: "char \<Rightarrow> char" where
  "map_escape c \<equiv> case c of
      CHR ''\"'' \<Rightarrow> CHR ''\"''
    | CHR 0x5C   \<Rightarrow> CHR 0x5C
    | CHR ''/''  \<Rightarrow> CHR ''/''
    | CHR ''b''  \<Rightarrow> CHR 0x08
    | CHR ''f''  \<Rightarrow> CHR 12
    | CHR ''n''  \<Rightarrow> CHR ''\<newline>''
    | CHR ''r''  \<Rightarrow> CHR 13
    | CHR ''t''  \<Rightarrow> CHR 0x09
    | _ \<Rightarrow> c"

definition map_int where
  "map_int c s \<equiv>
  let
    n  = string_to_nat s;
    neg  = (c = CHR ''-'');
    num = JsonNumber neg n None False None
   in Inr (TNum, LNum num)"

definition map_rat where
  "map_rat c s \<equiv>
  let
    ns = takeWhile (\<lambda>c. c \<noteq> CHR ''.'') s;
    fs = tl (dropWhile (\<lambda>c. c \<noteq> CHR ''.'') s);
    n  = string_to_nat ns;
    neg  = (c = CHR ''-'');
    num = JsonNumber neg n (Some fs) False None
   in Inr (TNum, LNum num)"

definition map_rat_exp where
  "map_rat_exp c s \<equiv>
  let
    coeff_s = takeWhile (\<lambda>c. c \<noteq> CHR ''e'' \<and> c \<noteq> CHR ''E'') s;
    exp_s   = tl (dropWhile (\<lambda>c. c \<noteq> CHR ''e'' \<and> c \<noteq> CHR ''E'') s);
    
    exp_neg = (hd exp_s = CHR ''-'');
    exp_val = string_to_nat (if hd exp_s = CHR ''-'' \<or> hd exp_s = CHR ''+'' 
                             then tl exp_s else exp_s);

    ns = takeWhile (\<lambda>c. c \<noteq> CHR ''.'') coeff_s;
    fs = (let rem = dropWhile (\<lambda>c. c \<noteq> CHR ''.'') coeff_s in 
          if rem = [] then [] else tl rem);
    
    n  = string_to_nat ns;
    neg  = (c = CHR ''-'');
    num = JsonNumber neg n (Some fs) exp_neg (Some exp_val)
   in Inr (TNum, LNum num)"

definition map_rat_int where
  "map_rat_int c s \<equiv>
  if CHR ''e'' \<in> set s \<or> CHR ''E'' \<in> set s then
    map_rat_exp c s
  else if CHR ''.'' \<in> set s then
    map_rat c s
  else
    map_int c s"

definition hex_val :: "char \<Rightarrow> nat" where
  "hex_val c = (let n = of_char c :: nat in
     (if of_char CHR ''0'' \<le> n \<and> n \<le> of_char CHR ''9'' then
        n - of_char CHR ''0''
      else if of_char CHR ''A'' \<le> n \<and> n \<le> of_char CHR ''F'' then
        10 + n - of_char CHR ''A''
      else 10 + n - of_char CHR ''a''))"

definition hex4_to_nat :: "char list \<Rightarrow> nat" where
  "hex4_to_nat cs = horner_sum hex_val 16 (rev cs)"

definition utf8_encode_bmp :: "nat \<Rightarrow> string" where
  "utf8_encode_bmp u =
     (if u < 0x80 then
        [char_of u]
      else if u < 0x800 then
        [ char_of (0xC0 + u div 64),
          char_of (0x80 + u mod 64) ]
      else
        [ char_of (0xE0 + u div 4096),
          char_of (0x80 + (u div 64) mod 64),
          char_of (0x80 + u mod 64) ])"

definition decode_unicode_escape :: "string \<Rightarrow> string" where
  "decode_unicode_escape cs =
     utf8_encode_bmp (hex4_to_nat cs)"

definition lex_node ::
  "(char + terminal \<times> lex) list list \<Rightarrow> lterminal + terminal \<Rightarrow> (char + terminal \<times> lex) list" where
  "lex_node xs nt =
    (case nt of
       Inl LRoot \<Rightarrow> (case xs of
        [Inl c] # _ \<Rightarrow>
          if is_1_9 c \<or> c = CHR ''0'' \<or> c = CHR ''-'' then
          let (s, bs) = combine_strings xs
           in map_rat_int c s # bs
          else
            concat xs
       | _ \<Rightarrow> concat xs
       )
     | Inl LZero \<Rightarrow> concat xs
     | Inl LMinus \<Rightarrow> concat xs
     | Inl LStartStr \<Rightarrow> (
       let xs = (case xs of [Inl (CHR 0x5C)] # xs \<Rightarrow> xs | _ \<Rightarrow> xs);
           ys = concat xs;
           s  = List.maps (\<lambda>Inl c \<Rightarrow> [c]  | Inr (Str, LStr s) \<Rightarrow> s    | _ \<Rightarrow> '''') ys;
           s  = butlast s
        in [Inr (Str, LStr s)]
      )
     | Inl LStartInt \<Rightarrow>
       let (s, bs) = combine_strings xs
        in (Inr (Str, LStr s)) # bs 
     | Inl LStartFrac \<Rightarrow>
       let (s, bs) = combine_strings xs
        in (Inr (Str, LStr s)) # bs 
     | Inl LExp \<Rightarrow>
       let (s, bs) = combine_strings xs
        in (Inr (Str, LStr s)) # bs 
     | Inl LExpSign \<Rightarrow>
       let (s, bs) = combine_strings xs
        in (Inr (Str, LStr s)) # bs 
     | Inl LStartExp \<Rightarrow>
       let (s, bs) = combine_strings xs
        in (Inr (Str, LStr s)) # bs 
     | Inr Tru \<Rightarrow> [Inr (Tru, LNone)]
     | Inr Fls \<Rightarrow> [Inr (Fls, LNone)]
     | Inr Null \<Rightarrow> [Inr (Null, LNone)]
     | Inr Str \<Rightarrow>
       let xs = (case xs of [Inl (CHR 0x5C)] # xs \<Rightarrow> xs | _ \<Rightarrow> xs);
           ys = concat xs;
           s  = List.maps (\<lambda>Inl c \<Rightarrow> [c]  | Inr (Str, LStr s) \<Rightarrow> s    | _ \<Rightarrow> '''') ys
        in [Inr (Str, LStr s)]
     | Inl LEscape \<Rightarrow> (case xs of
         [[Inl c]] \<Rightarrow> [Inl (map_escape c)]
       | _ \<Rightarrow> tl (concat xs) \<comment> \<open>for unicode code points\<close>
       )
     | Inr LeftBrack  \<Rightarrow> [Inr (LeftBrack, LNone)]
     | Inr RightBrack \<Rightarrow> [Inr (RightBrack, LNone)]
     | Inr LeftBrace  \<Rightarrow> [Inr (LeftBrace, LNone)]
     | Inr RightBrace \<Rightarrow> [Inr (RightBrace, LNone)]
     | Inr Comma      \<Rightarrow> [Inr (Comma, LNone)]
     | Inr Colon      \<Rightarrow> [Inr (Colon, LNone)]
     | Inr TNum \<Rightarrow>
       let (s, bs) = combine_strings xs
        in (Inr (Str, LStr s)) # bs
     | Inl LFrac \<Rightarrow> concat xs
     | Inl LUnicode1 \<Rightarrow>
       let (s, _) = combine_strings xs;
                s = decode_unicode_escape s
        in [Inr (Str, LStr s)]
     | Inl LUnicode2 \<Rightarrow> concat xs
     | Inl LUnicode3 \<Rightarrow> concat xs
     | Inl LUnicode4 \<Rightarrow> concat xs
    )"

definition
  "lex_tree_to_lex_list xs = [sum.projr x . x \<leftarrow> fold_parse_tree lex_leaf lex_node xs, \<not> sum.isl x]"

paragraph \<open>Interlude: handling literal surrogates\<close>

text \<open>
JSON uses surrogate pairs like \<open>"\uD83D\uDE00"\<close>,
in this case to encode the grinning emoji \<open>U+1F600\<close>.
The lexer so far encodes this as the \<^emph>\<open>literal surrogate\<close> 6-byte sequence \<open>ED A0 BD ED B8 80\<close>.
This is invalid UTF-8 and should be encoded as \<open>F0 9F 98 80\<close> instead.
We therefore repair these intermediate literal surrogates.

Note that the input to the lexer is assumed to be valid UTF-8,
thus containing no literal surrogates.
\<close>

\<comment> \<open>Check if 3 bytes represent a High Surrogate (0xED 0xA0 0x80 - 0xED 0xAF 0xBF)\<close>
definition is_high_byte_seq :: "char \<Rightarrow> char \<Rightarrow> char \<Rightarrow> bool" where
  "is_high_byte_seq b1 b2 b3 \<longleftrightarrow>
    (nat_of_char b1 = 0xED \<and>
     nat_of_char b2 \<ge> 0xA0 \<and> nat_of_char b2 \<le> 0xAF \<and>
     nat_of_char b3 \<ge> 0x80 \<and> nat_of_char b3 \<le> 0xBF)"

\<comment> \<open>Check if 3 bytes represent a Low Surrogate (0xED 0xB0 0x80 - 0xED 0xBF 0xBF)\<close>
definition is_low_byte_seq :: "char \<Rightarrow> char \<Rightarrow> char \<Rightarrow> bool" where
  "is_low_byte_seq b1 b2 b3 \<longleftrightarrow>
    (nat_of_char b1 = 0xED \<and>
     nat_of_char b2 \<ge> 0xB0 \<and> nat_of_char b2 \<le> 0xBF \<and>
     nat_of_char b3 \<ge> 0x80 \<and> nat_of_char b3 \<le> 0xBF)"

definition extract_10_bits :: "char \<Rightarrow> char \<Rightarrow> nat" where
  "extract_10_bits b2 b3 = ((nat_of_char b2 mod 16) * 64 + (nat_of_char b3 mod 64))"

definition encode_utf8_4 :: "nat \<Rightarrow> nat \<Rightarrow> char list" where
  "encode_utf8_4 hi_bits lo_bits = (
     let u = (hi_bits * 1024) + lo_bits + 65536 in
     [char_of (240 + (u div 262144)),             \<comment> \<open>0xF0 + bits\<close>
      char_of (128 + ((u div 4096) mod 64)),      \<comment> \<open>0x80 + bits\<close>
      char_of (128 + ((u div 64) mod 64)),        \<comment> \<open>0x80 + bits\<close>
      char_of (128 + (u mod 64))])"               \<comment> \<open>0x80 + bits\<close>

fun repair_bytes :: "string \<Rightarrow> string option" where
  "repair_bytes (h1 # h2 # h3 # l1 # l2 # l3 # cs) = (
     if is_high_byte_seq h1 h2 h3 \<and> is_low_byte_seq l1 l2 l3 then
       (case repair_bytes cs of
          Some rest \<Rightarrow> Some (encode_utf8_4 (extract_10_bits h2 h3) (extract_10_bits l2 l3) @ rest)
        | None \<Rightarrow> None)
     else if is_high_byte_seq h1 h2 h3 then None \<comment> \<open>Lone High\<close>
     else (case repair_bytes (h2 # h3 # l1 # l2 # l3 # cs) of
             Some rest \<Rightarrow> Some (h1 # rest) | None \<Rightarrow> None)
  )" |
  "repair_bytes (b1 # b2 # b3 # cs) = (
     if is_high_byte_seq b1 b2 b3 \<or> is_low_byte_seq b1 b2 b3 then None
     else (case repair_bytes (b2 # b3 # cs) of Some rest \<Rightarrow> Some (b1 # rest) | None \<Rightarrow> None)
  )" |
  "repair_bytes (c # cs) = (case repair_bytes cs of Some rest \<Rightarrow> Some (c # rest) | None \<Rightarrow> None)" |
  "repair_bytes [] = Some []"

\<comment> \<open>Repairing the surrogate for the grinning emoji\<close>
lemma "repair_bytes [CHR 0xED, CHR 0xA0, CHR 0xBD, CHR 0xED, CHR 0xB8, CHR 0x80]
  = Some [CHR 0xF0, CHR 0x9F, CHR 0x98, CHR 0x80]"
  by eval

\<comment> \<open>Lone surrogates are rejected\<close>
lemma
  "repair_bytes [CHR 0xED, CHR 0xA0, CHR 0xBD] = None"
  by eval

\<comment> \<open>ASCII strings are unchanged\<close>
lemma
  "repair_bytes ''test'' = Some ''test''"
  by eval

fun map_surrogates_lex where
  "map_surrogates_lex (LStr x) = map_option LStr (repair_bytes x)"
| "map_surrogates_lex x = Some x"

definition map_surrogates where
  "map_surrogates ps = those (
    map (\<lambda>(k, v). map_option (Product_Type.Pair k) (map_surrogates_lex v)) ps)"

subsection \<open>Putting everything together\<close>

definition lex_it where
  "lex_it x \<equiv>
  let
    chrs = mk_chrs x;
    lex_result = parse lex_pt (NT (start jsonLex)) chrs
  in
    case lex_result of
      RESULT t r _ \<Rightarrow>
      if r = [] then
        case map_surrogates (lex_tree_to_lex_list t) of
          None \<Rightarrow> Inl ''Lone surrogates not allowed''
        | Some ps \<Rightarrow> Inr ps
      else
        Inl ''Remaining characters''
    | REJECT e _ \<Rightarrow> Inl e"

definition parse_it where
  "parse_it x \<equiv>
  let
    result = parse pt (NT (start jsonGrammar)) x
   in
    case result of
      RESULT t r _ \<Rightarrow>
      if r = [] then
        Inr (parse_tree_to_json t)
      else
        Inl ''Remaining tokens''
    | REJECT e _ \<Rightarrow> Inl e"

definition
  "json_from_string x \<equiv>
  case lex_it x of
    Inr t \<Rightarrow> (case parse_it t of
      Inr x \<Rightarrow> Inr x
    | Inl e \<Rightarrow> Inl (''Parsing error: '' @ e))
  | Inl e \<Rightarrow> Inl (''Lexing error: '' @ e)"

subsection \<open>Examples\<close>

definition ex1 :: string where
  "ex1 \<equiv> ''
  {
  \"items\": [
    {
    \"id\":           65,
    \"description\":  \"Title\",
    \"visible\":      false},
    {
    \"id\":           42,
    \"visible\":      true}
  ]
}''
"

definition
  "json_int i = JSON.Num (JsonNumber (i < 0) (nat (abs i)) None False None)"

lemma "json_from_string ex1 = Inr (
  Object
  [(''items'',
    Array
     [Object
       [(''id'', json_int 65),
        (''description'', String ''Title''),
        (''visible'', Boolean False)],
      Object
       [(''id'', json_int 42), (''visible'', Boolean True)]])])"
  by eval

lemma "json_from_string ''{\"test\": null, \"test\": 67}''
  = Inr (Object [(''test'', JSON.Nil), (''test'', json_int 67)])"
  by eval

lemma "json_from_string ''{\"test\": null, \"test\": [67], \"a\": false}''
  = Inr (Object [(''test'', JSON.Nil), (''test'', Array [json_int 67]), (''a'', Boolean False)])"
  by eval

lemma "json_from_string ''\",+-0][{}\"'' = Inr (String '',+-0][{}'')"
  by eval

lemma "json_from_string ''\"\"'' = Inr (String [])"
  by eval

lemma "json_from_string ''\"a\"'' = Inr (String ''a'')"
  by eval

text \<open>Escape characters\<close>
lemma "json_from_string (
    CHR ''\"'' # CHR 0x5C # ''\"cb'' @ CHR 0x5C # ''n'' @ CHR 0x5C # CHR 0x5C
  # CHR 0x5C # ''b'' @ CHR 0x5C # ''r'' @ CHR 0x5C # ''t\"'')
  = Inr (String
      [CHR ''\"'', CHR ''c'', CHR ''b'', CHR ''\<newline>'', CHR 0x5C, CHR 8, CHR 13, CHR 9])"
  by eval

lemma "json_from_string ''[-0]'' = Inr (JSON.Array [JSON.Num (JsonNumber True 0 None False None)])"
  by eval

lemma "json_from_string ''[1,2, 123,1, 0,\<newline>-1,-12]''
  = Inr (Array (map json_int [1, 2, 123, 1, 0, -1, - 12]))"
  by eval

lemma "json_from_string ''[1.0,1.021,0.2]''
  = Inr (Array
       [Num (JsonNumber False 1 (Some ''0'')  False None),
        Num (JsonNumber False 1 (Some ''021'') False None),
        Num (JsonNumber False 0 (Some ''2'')  False None)])"
  by eval

lemma
  "json_from_string ''[12E-2, 1e2, 33E+2 , 3.3E+2,-1.3e-23, 1.3E0, 1e-0, -0e+0000]''
  = Inr (Array
       [Num (JsonNumber False 12 (Some []) True (Some 2)),
        Num (JsonNumber False 1 (Some []) False (Some 2)),
        Num (JsonNumber False 33 (Some []) False (Some 2)),
        Num (JsonNumber False 3 (Some ''3'') False (Some 2)),
        Num (JsonNumber True 1 (Some ''3'') True (Some 23)),
        Num (JsonNumber False 1 (Some ''3'') False (Some 0)),
        Num (JsonNumber False 1 (Some []) True (Some 0)),
        Num (JsonNumber True 0 (Some []) False (Some 0))])"
  by eval

lemma "json_from_string ''\"a\",'' = Inl ''Parsing error: Remaining tokens''"
  by eval

lemma "json_from_string ''00'' = Inl ''Lexing error: lookup failure''"
  by eval

lemma "json_from_string (''\"a'' @ CHR 0x5C # ''ud800\"'')
  = Inl ''Lexing error: Lone surrogates not allowed''"
  by eval

\<comment> \<open>\<open>U+1F600\<close>\<close>
lemma "json_from_string (''\"'' @ CHR 0x5C # ''uD83D'' @ CHR 0x5C # ''uDE00\"'')
  = Inr (String [CHR 0xF0, CHR 0x9F, CHR 0x98, CHR 0x80])"
  by eval

\<comment> \<open>\<open>\<lambda>\<close>\<close>
lemma "json_from_string (''\"'' @ CHR 0x5C # ''u03BB\"'')
  = Inr (String [CHR 0xCE, CHR 0xBB])"
  by eval

\<comment> \<open>\<open>"a "\<close>\<close>
lemma "json_from_string (''\"a'' @ CHR 0x5C # ''u0020\"'') = Inr (String ''a '')"
  by eval

subsection \<open>Printing JSON\<close>

definition
  "pad m s = replicate m CHR '' '' @ s"

definition app where "app a b \<equiv> b a"

notation (input) app (infixl "|>" 59)

fun intersperse :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "intersperse sep (x # y # xs) = x # sep # intersperse sep (y # xs)"
| "intersperse _ xs = xs"

fun hex_digit :: "nat \<Rightarrow> char" where
  "hex_digit n =
     (if n < 10 then char_of (48 + n) else char_of (55 + n))"

fun hex2 :: "nat \<Rightarrow> string" where
  "hex2 n =
     [hex_digit (n div 16), hex_digit (n mod 16)]"

fun escape_char :: "char \<Rightarrow> string" where
  "escape_char c =
     (if c = CHR 0x22 then
        [CHR 0x5C, CHR 0x22]      \<comment> \<open>\<open>\"\<close>\<close>
      else if c = CHR 0x5C then
        [CHR 0x5C, CHR 0x5C]      \<comment> \<open>\<open>\\\<close>\<close>
      else if c = CHR 0x08 then
        [CHR 0x5C, CHR 0x62]      \<comment> \<open>\<open>\\b\<close>\<close>
      else if c = CHR 0x0C then
        [CHR 0x5C, CHR 0x66]      \<comment> \<open>\<open>\\f\<close>\<close>
      else if c = CHR 0x0A then
        [CHR 0x5C, CHR 0x6E]      \<comment> \<open>\<open>\\n\<close>\<close>
      else if c = CHR 0x0D then
        [CHR 0x5C, CHR 0x72]      \<comment> \<open>\<open>\\r\<close>\<close>
      else if c = CHR 0x09 then
        [CHR 0x5C, CHR 0x74]      \<comment> \<open>\<open>\\t\<close>\<close>
      else if nat_of_char c < 32 then
        [CHR 0x5C, CHR 0x75, CHR 0x30, CHR 0x30]
          @ hex2 (nat_of_char c)  \<comment> \<open>\<open>\\u00XX\<close>\<close>
      else
        [c])"

fun escape_string :: "string \<Rightarrow> string" where
  "escape_string [] = []"
| "escape_string (c # cs) = escape_char c @ escape_string cs"

fun shows_json_number where
  "shows_json_number (JsonNumber s n None se None) = (if s then ''-'' else '''') @ show n"
| "shows_json_number (JsonNumber s n (Some f) se None)
  = (if s then ''-'' else '''') @ show n @ ''.'' @ f"
| "shows_json_number (JsonNumber s n None se (Some e))
  = (if s then ''-'' else '''') @ show n @ ''E'' @ (if se then ''-'' else '''') @ show e"
| "shows_json_number (JsonNumber s n (Some f) se (Some e))
  = (if s then ''-'' else '''') @ show n @ ''.'' @ f @ ''E'' @ (if se then ''-'' else '''') @ show e"

fun shows_json :: "nat \<Rightarrow> JSON \<Rightarrow> string" where
  "shows_json n (Num m) = shows_json_number m |> pad n"
| "shows_json n (Boolean b) = (if b then ''true'' else ''false'') |> pad n"
| "shows_json n Nil = ''null'' |> pad n"
| "shows_json n (String s) = pad n (''\"'' @ escape_string s @ ''\"'')"
| "shows_json n (JSON.Array xs) = (
  if xs = [] then
    pad n ''[]''
  else
    pad n ''[\<newline>''
    @ concat (map (shows_json (n + 2)) xs |> intersperse '',\<newline>'')
    @ ''\<newline>''
    @ pad n '']''
  )"
| "shows_json n (JSON.Object xs) = (
  if xs = [] then
    pad n ''{}''
  else
    pad n ''{\<newline>''
    @ concat (
      map (\<lambda>(k, v).
        pad (n + 2) (''\"'' @ escape_string k @ ''\"'') @ '':\<newline>'' @ shows_json (n + 4) v) xs
      |> intersperse '',\<newline>''
    )
    @ ''\<newline>''
    @ pad n ''}''
  )"

instantiation JSON :: "show"
begin

definition "shows_prec p (x :: JSON) rest = shows_json 0 x @ rest" for p

definition "shows_list jsons s =
  map (shows_json 0) jsons |> intersperse '', '' |> (\<lambda>xs. ''['' @ concat xs @ '']'' @ s)"
instance
  by standard (simp_all add: shows_prec_JSON_def shows_list_JSON_def show_law_simps app_def)

end

no_notation (input) app (infixl "|>" 59)

paragraph \<open>Testing round-trips\<close>

lemma
  "json_from_string (show (sum.projr (json_from_string ex1))) = json_from_string ex1"
  by eval

definition
  "rm_ws s = [c . c \<leftarrow> s, \<not> is_ws c]"

\<comment> \<open>This property will not generally hold in the presence of escaped unicode characters.\<close>
lemma "rm_ws (show (sum.projr (json_from_string ex1))) = rm_ws ex1"
  by eval

definition ex_rcf8259 where
  "ex_rcf8259 \<equiv>
''{
  \"Image\": {
      \"Width\":  800,
      \"Height\": 600,
      \"Title\":  \"View from 15th Floor\",
      \"Thumbnail\": {
          \"Url\":    \"http://www.example.com/image/481989943\",
          \"Height\": 125,
          \"Width\":  100
      },
      \"Animated\" : false,
      \"IDs\": [116, 943, 234, 38793]
    }
}''"

lemma
  "json_from_string (show (sum.projr (json_from_string ex_rcf8259))) = json_from_string ex_rcf8259"
  by eval

lemma "rm_ws (show (sum.projr (json_from_string ex_rcf8259))) = rm_ws ex_rcf8259"
  by eval

end