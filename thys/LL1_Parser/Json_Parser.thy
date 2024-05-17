subsection \<open>Generating a JSON Parser\<close>

theory Json_Parser
  imports LL1_Parser_show "Show.Show_Instances"
begin

datatype terminal =
    TInt
  | Float
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
    (Value, [T TInt]),
    (Value, [T Float]),
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

datatype lex =
    LInt (lex_int: int)
  | LFloat
  | LStr (lex_str: string)
  | LNone

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
  "IntS s = (TInt, LInt s)"

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
   []"
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
   []"
  by eval

subsection \<open>Reading the Parse Tree\<close>

\<comment> \<open>A datatype for JSON (taken from Munta)\<close>
datatype JSON =
  Object "(string \<times> JSON) list"
| Array "JSON list"
| String string \<comment>\<open>An Isabelle string rather than a JSON string\<close>
| Int int \<comment>\<open>The number type is split into natural Isabelle/HOL types\<close>
| Nat nat
| Rat nat int
| Boolean bool \<comment>\<open>True and False are contracted to one constructor\<close>
| Nil

primrec fold_parse_tree :: "('t \<Rightarrow> 'a) \<Rightarrow> ('a list \<Rightarrow> 'n \<Rightarrow> 'a) \<Rightarrow> ('n, 't) parse_tree \<Rightarrow> 'a"
where
  "fold_parse_tree t n (Leaf x) = t x"
| "fold_parse_tree t n (Node x ts) = n (map (fold_parse_tree t n) ts) x"

definition
  "json_leaf \<equiv> \<lambda>(t, s). (case t of
    Str => JSON.String (lex_str s) |
    TInt => JSON.Int (lex_int s) |
    Float \<Rightarrow> JSON.Rat 1 0 |
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
  "the_RESULT = (\<lambda>RESULT r _ \<Rightarrow> r)"

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
         [(''id'', JSON.Int 65), (''description'', String ''Title''),
          (''visible'', Boolean False)],
        Object [(''id'', JSON.Int 42), (''visible'', Boolean True)]])]"
  by eval

text \<open>
Note that in Vermillion one can attach the functions to read parse trees directly
to the production rules.
While this would be possible in Isabelle/HOL, it would give little advantage over defining
the reader function directly, since we are missing dependent types.
\<close>

end