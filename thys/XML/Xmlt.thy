(*
Author:  Akihisa Yamada <ayamada@trs.cm.is.nagoya-u.ac.jp> 
Author:  Christian Sternagel <c.sternagel@gmail.com> (
Author:  René Thiemann <rene.thiemann@uibk.ac.at> 
*)
theory Xmlt
  imports
    "HOL-Library.Extended_Nat"
    Show.Number_Parser
    Certification_Monads.Strict_Sum
    Show.Shows_Literal
    Xml
begin

text \<open>String literals in parser, for nicer generated code\<close>
type_synonym ltag = String.literal 

datatype 'a xml_error = TagMismatch "ltag list" | Fatal 'a
text \<open>
  @{term "TagMismatch tags"} represents tag mismatch, expecting one of @{term tags} but
  something else is encountered.
\<close>

lemma xml_error_mono [partial_function_mono]:
  assumes p1: "\<And>tags. mono_option (p1 tags)"
    and p2: "\<And>x. mono_option (p2 x)"
    and f: "mono_option f"
  shows "mono_option (\<lambda>g. case s of TagMismatch tags \<Rightarrow> p1 tags g | Fatal x \<Rightarrow> p2 x g)"
  using assms by (cases s, auto intro!:partial_function_mono)

text \<open>A state is a tuple of
  the XML or list of XMLs to be parsed,
  the attributes,
  a flag indicating if mismatch is allowed,
  a list of tags that have been mismatched,
  the current position.
\<close>
type_synonym 'a xmlt = "xml \<times> (string \<times> string) list \<times> bool \<times> ltag list \<times> ltag list \<Rightarrow> String.literal xml_error +\<^sub>\<bottom> 'a"
type_synonym 'a xmlst = "xml list \<times> (string \<times> string) list \<times> bool \<times> ltag list \<times> ltag list \<Rightarrow> String.literal xml_error +\<^sub>\<bottom> 'a"

lemma xml_state_cases:
  assumes "\<And>p nam atts xmls. x = (XML nam atts xmls, p) \<Longrightarrow> thesis"
    and "\<And>p txt. x = (XML_text txt, p) \<Longrightarrow> thesis"
  shows thesis
  using assms by (cases x; cases "fst x", auto)

lemma xmls_state_cases:
  assumes "\<And>p. x = ([],p) \<Longrightarrow> thesis"
    and "\<And>xml xmls p. x = (xml # xmls, p) \<Longrightarrow> thesis"
  shows thesis
  using assms by (cases x; cases "fst x", auto)

lemma xmls_state_induct:
  fixes x :: "xml list \<times> _"
  assumes "\<And>a b c d. P ([],a,b,c,d)"
    and "\<And>xml xmls a b c d. (\<And>a b c d. P (xmls,a,b,c,d)) \<Longrightarrow> P (xml # xmls, a, b, c, d)"
  shows "P x"
proof (induct x)
  case (fields xmls a b c d)
  with assms show ?case by (induct xmls arbitrary:a b c d, auto)
qed

definition xml_error
  where "xml_error str x \<equiv> case x of (xmls,_,_,_,pos) \<Rightarrow>
  let next = case xmls of
      XML tag _ _ # _ \<Rightarrow> STR ''<'' + String.implode tag + STR ''>''
    | XML_text str # _ \<Rightarrow> STR ''text element \"'' + String.implode str + STR ''\"''
    | [] \<Rightarrow> STR ''tag close''
  in
  Left (Fatal (STR ''parse error on '' + next + STR '' at '' + default_showsl_list showsl_lit pos (STR '''') + STR '':\<newline>'' + str))"

definition xml_return :: "'a \<Rightarrow> 'a xmlst"
  where "xml_return v x \<equiv> case x
  of ([],_) \<Rightarrow> Right v
  | _ \<Rightarrow> xml_error (STR ''expecting tag close'') x"

definition "mismatch tag x \<equiv> case x of
  (xmls,atts,flag,cands,_) \<Rightarrow>
    if flag then Left (TagMismatch (tag#cands))
    else xml_error (STR ''expecting '' + default_showsl_list showsl_lit (tag#cands) (STR '''')) x"

abbreviation xml_any :: "xml xmlt"
  where
    "xml_any x \<equiv> Right (fst x)"

text \<open>Conditional parsing depending on tag match.\<close>

definition bind2 :: "'a +\<^sub>\<bottom>'b \<Rightarrow> ('a \<Rightarrow> 'c +\<^sub>\<bottom> 'd) \<Rightarrow> ('b \<Rightarrow> 'c +\<^sub>\<bottom> 'd) \<Rightarrow> 'c +\<^sub>\<bottom> 'd" where
  "bind2 x f g = (case x of 
      Bottom \<Rightarrow> Bottom
    | Left a \<Rightarrow> f a
    | Right b \<Rightarrow> g b)" 

lemma bind2_cong[fundef_cong]: "x = y \<Longrightarrow> (\<And> a. y = Left a \<Longrightarrow> f1 a = f2 a) \<Longrightarrow> 
  (\<And> b. y = Right b \<Longrightarrow> g1 b = g2 b) \<Longrightarrow> bind2 x f1 g1 = bind2 y f2 g2" 
  by (cases x, auto simp: bind2_def)

lemma bind2_code[code]:
  "bind2 (sumbot a) f g = (case a of Inl a \<Rightarrow> f a | Inr b \<Rightarrow> g b)"
  by (cases a) (auto simp: bind2_def)

definition xml_or (infixr \<open>XMLor\<close> 51)
  where
    "xml_or p1 p2 x \<equiv> case x of (x1,atts,flag,cands,rest) \<Rightarrow> (
  bind2 (p1 (x1,atts,True,cands,rest))
    (\<lambda> err1. case err1
    of TagMismatch cands1 \<Rightarrow> p2 (x1,atts,flag,cands1,rest)
    | err1 \<Rightarrow> Left err1)
    Right)" 

definition xml_do :: "ltag \<Rightarrow> 'a xmlst \<Rightarrow> 'a xmlt" where
  "xml_do tag p x \<equiv>
  case x of (XML nam atts xmls, _, flag, cands, pos) \<Rightarrow>
    if nam = String.explode tag then p (xmls,atts,False,[],tag#pos) \<comment> \<open>inner tag mismatch is not allowed\<close>
    else mismatch tag ([fst x], snd x)
   | _ \<Rightarrow> mismatch tag ([fst x], snd x)"

text \<open>parses the first child\<close>
definition xml_take :: "'a xmlt \<Rightarrow> ('a \<Rightarrow> 'b xmlst) \<Rightarrow> 'b xmlst"
  where "xml_take p1 p2 x \<equiv>
  case x of ([],rest) \<Rightarrow> (
    \<comment> \<open>Only for accumulating expected tags.\<close>
    bind2 (p1 (XML [] [] [], rest)) Left (\<lambda> a. Left (Fatal (STR ''unexpected'')))
  )
  | (x#xs,atts,flag,cands,rest) \<Rightarrow> (
      bind2 (p1 (x,atts,flag,cands,rest)) Left
        (\<lambda> a. p2 a (xs,atts,False,[],rest))) \<comment> \<open>If one child is parsed, then later mismatch is not allowed\<close>"

definition xml_take_text :: "(string \<Rightarrow> 'a xmlst) \<Rightarrow> 'a xmlst" where
  "xml_take_text p xs \<equiv>
   case xs of (XML_text text # xmls, s) \<Rightarrow> p text (xmls,s)
   | _ \<Rightarrow> xml_error (STR ''expecting a text'') xs"

definition xml_take_int :: "(int \<Rightarrow> 'a xmlst) \<Rightarrow> 'a xmlst" where
  "xml_take_int p xs \<equiv>
  case xs of (XML_text text # xmls, s) \<Rightarrow>
    (case int_of_string text of Inl x \<Rightarrow> xml_error x xs | Inr n \<Rightarrow> p n (xmls,s))
  | _ \<Rightarrow> xml_error (STR ''expecting an integer'') xs"

definition xml_take_nat :: "(nat \<Rightarrow> 'a xmlst) \<Rightarrow> 'a xmlst" where
  "xml_take_nat p xs \<equiv>
  case xs of (XML_text text # xmls, s) \<Rightarrow>
    (case nat_of_string text of Inl x \<Rightarrow> xml_error x xs | Inr n \<Rightarrow> p n (xmls,s))
  | _ \<Rightarrow> xml_error (STR ''expecting a number'') xs"

definition xml_leaf where
  "xml_leaf tag ret \<equiv> xml_do tag (xml_return ret)"

definition xml_text :: "ltag \<Rightarrow> string xmlt" where
  "xml_text tag \<equiv> xml_do tag (xml_take_text xml_return)"

definition xml_int :: "ltag \<Rightarrow> int xmlt" where
  "xml_int tag \<equiv> xml_do tag (xml_take_int xml_return)"

definition xml_nat :: "ltag \<Rightarrow> nat xmlt" where
  "xml_nat tag \<equiv> xml_do tag (xml_take_nat xml_return)"

definition bool_of_string :: "string \<Rightarrow> String.literal + bool"
  where
    "bool_of_string s \<equiv>
    if s = ''true'' then Inr True
    else if s = ''false'' then Inr False
    else Inl (STR ''cannot convert \"'' + String.implode s + STR ''\" into Boolean'')"

definition xml_bool :: "ltag \<Rightarrow> bool xmlt"
  where
    "xml_bool tag x \<equiv>
    bind2 (xml_text tag x) Left
     (\<lambda> str. ( case bool_of_string str of Inr b \<Rightarrow> Right b
        | Inl err \<Rightarrow> xml_error err ([fst x], snd x)
      ))"


definition xml_change :: "'a xmlt \<Rightarrow> ('a \<Rightarrow> 'b xmlst) \<Rightarrow> 'b xmlt" where
  "xml_change p f x \<equiv>
    bind2 (p x) Left (\<lambda> a. case x of (_,rest) \<Rightarrow> f a ([],rest))"


text \<open>
  Parses the first child, if tag matches.
\<close>
definition xml_take_optional :: "'a xmlt \<Rightarrow> ('a option \<Rightarrow> 'b xmlst) \<Rightarrow> 'b xmlst"
  where "xml_take_optional p1 p2 xs \<equiv>
  case xs of ([],_) \<Rightarrow> p2 None xs
  | (xml # xmls, atts, allow, cands, rest) \<Rightarrow> 
    bind2 (p1 (xml, atts, True, cands, rest))
      (\<lambda> e. case e of 
              TagMismatch cands1 \<Rightarrow> p2 None (xml#xmls, atts, allow, cands1, rest) \<comment> \<open>TagMismatch is allowed\<close>
            | _ \<Rightarrow> Left e)
      (\<lambda> a. p2 (Some a) (xmls, atts, False, [], rest))" 

definition xml_take_default :: "'a \<Rightarrow> 'a xmlt \<Rightarrow> ('a \<Rightarrow> 'b xmlst) \<Rightarrow> 'b xmlst"
  where "xml_take_default a p1 p2 xs \<equiv>
  case xs of ([],_) \<Rightarrow> p2 a xs
  | (xml # xmls, atts, allow, cands, rest) \<Rightarrow> (
    bind2 (p1 (xml, atts, True, cands, rest)) 
      (\<lambda> e. case e of 
              TagMismatch cands1 \<Rightarrow> p2 a (xml#xmls, atts, allow, cands1, rest)  \<comment> \<open>TagMismatch is allowed\<close>
            | _ \<Rightarrow> Left e) 
      (\<lambda>a. p2 a (xmls, atts, False, [], rest)))"

text \<open>Take first children, as many as tag matches.\<close>

fun xml_take_many_sub :: "'a list \<Rightarrow> nat \<Rightarrow> enat \<Rightarrow> 'a xmlt \<Rightarrow> ('a list \<Rightarrow> 'b xmlst) \<Rightarrow> 'b xmlst" where
  "xml_take_many_sub acc minOccurs maxOccurs p1 p2 ([], atts, allow, rest) = (
    if minOccurs = 0 then p2 (rev acc) ([], atts, allow, rest)
    else \<comment> \<open>only for nice error log\<close>
      bind2 (p1 (XML [] [] [], atts, False, rest)) Left (\<lambda> _. Left (Fatal (STR ''unexpected'')))
  )"
| "xml_take_many_sub acc minOccurs maxOccurs p1 p2 (xml # xmls, atts, allow, cands, rest) = (
      if maxOccurs = 0 then p2 (rev acc) (xml # xmls, atts, allow, cands, rest)
      else
        bind2 (p1 (xml, atts, minOccurs = 0, cands, rest))
          (\<lambda> e. case e of 
                  TagMismatch tags \<Rightarrow> p2 (rev acc) (xml # xmls, atts, allow, cands, rest)
                | _ \<Rightarrow> Left e)
          (\<lambda> a. xml_take_many_sub (a # acc) (minOccurs-1) (maxOccurs-1) p1 p2 (xmls, atts, False, [], rest))
  )"

abbreviation xml_take_many where "xml_take_many \<equiv> xml_take_many_sub []"

fun pick_up where
  "pick_up rest key [] = None"
| "pick_up rest key ((l,r)#s) = (if key = l then Some (r,rest@s) else pick_up ((l,r)#rest) key s)"

definition xml_take_attribute :: "ltag \<Rightarrow> (string \<Rightarrow> 'a xmlst) \<Rightarrow> 'a xmlst"
  where "xml_take_attribute att p xs \<equiv>
  case xs of (xmls,atts,allow,cands,pos) \<Rightarrow> (
    case pick_up [] (String.explode att) atts of
      None \<Rightarrow> xml_error (STR ''attribute \"'' + att + STR ''\" not found'') xs
    | Some(v,rest) \<Rightarrow> p v (xmls,rest,allow,cands,pos)
  )"

definition xml_take_attribute_optional :: "ltag \<Rightarrow> (string option \<Rightarrow> 'a xmlst) \<Rightarrow> 'a xmlst"
  where "xml_take_attribute_optional att p xs \<equiv>
  case xs of (xmls,atts,info) \<Rightarrow> (
    case pick_up [] (String.explode att) atts of
      None \<Rightarrow> p None xs
    | Some(v,rest) \<Rightarrow> p (Some v) (xmls,rest,info)
  )"

definition xml_take_attribute_default :: "string \<Rightarrow> ltag \<Rightarrow> (string \<Rightarrow> 'a xmlst) \<Rightarrow> 'a xmlst"
  where "xml_take_attribute_default def att p xs \<equiv>
  case xs of (xmls,atts,info) \<Rightarrow> (
    case pick_up [] (String.explode att) atts of
      None \<Rightarrow> p def xs
    | Some(v,rest) \<Rightarrow> p v (xmls,rest,info)
  )"

nonterminal xml_binds and xml_bind
syntax
  "_xml_block" :: "xml_binds \<Rightarrow> 'a" (\<open>XMLdo {//(2  _)//}\<close> [12] 1000)
  "_xml_take"  :: "pttrn \<Rightarrow> 'a \<Rightarrow> xml_bind" (\<open>(2_ \<leftarrow>/ _)\<close> 13)
  "_xml_take_text"  :: "pttrn \<Rightarrow> xml_bind" (\<open>(2_ \<leftarrow>text)\<close> 13)
  "_xml_take_int"  :: "pttrn \<Rightarrow> xml_bind" (\<open>(2_ \<leftarrow>int)\<close> 13)
  "_xml_take_nat"  :: "pttrn \<Rightarrow> xml_bind" (\<open>(2_ \<leftarrow>nat)\<close> 13)
  "_xml_take_att"  :: "pttrn \<Rightarrow> ltag \<Rightarrow> xml_bind" (\<open>(2_ \<leftarrow>att/ _)\<close> 13)
  "_xml_take_att_optional" :: "pttrn \<Rightarrow> ltag \<Rightarrow> xml_bind" (\<open>(2_ \<leftarrow>att?/ _)\<close> 13)
  "_xml_take_att_default" :: "pttrn \<Rightarrow> ltag \<Rightarrow> string \<Rightarrow> xml_bind" (\<open>(2_ \<leftarrow>att[(_)]/ _)\<close> 13)
  "_xml_take_optional" :: "pttrn \<Rightarrow> 'a \<Rightarrow> xml_bind" (\<open>(2_ \<leftarrow>?/ _)\<close> 13)
  "_xml_take_default" :: "pttrn \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> xml_bind" (\<open>(2_ \<leftarrow>[(_)]/ _)\<close> 13)
  "_xml_take_all" :: "pttrn \<Rightarrow> 'a \<Rightarrow> xml_bind" (\<open>(2_ \<leftarrow>*/ _)\<close> 13)
  "_xml_take_many" :: "pttrn \<Rightarrow> nat \<Rightarrow> enat \<Rightarrow> 'a \<Rightarrow> xml_bind" (\<open>(2_ \<leftarrow>^{(_)..(_)}/ _)\<close> 13)
  "_xml_let" :: "pttrn \<Rightarrow> 'a \<Rightarrow> xml_bind" (\<open>(2let _ =/ _)\<close> [1000, 13] 13)
  "_xml_final" :: "'a xmlst \<Rightarrow> xml_binds" (\<open>_\<close>)
  "_xml_cons" :: "xml_bind \<Rightarrow> xml_binds \<Rightarrow> xml_binds" (\<open>_;//_\<close> [13, 12] 12)
  "_xml_do" :: "ltag \<Rightarrow> xml_binds \<Rightarrow> 'a" (\<open>XMLdo (_) {//(2 _)//}\<close> [1000,12] 1000)

syntax (ASCII)
  "_xml_take" :: "pttrn \<Rightarrow> 'a \<Rightarrow> xml_bind" (\<open>(2_ <-/ _)\<close> 13)

translations
  "_xml_block (_xml_cons (_xml_take p x) (_xml_final e))"
  \<rightleftharpoons> "_xml_block (_xml_final (CONST xml_take x (\<lambda>p. e)))"
  "_xml_block (_xml_cons (_xml_take_text p) (_xml_final e))"
  \<rightleftharpoons> "_xml_block (_xml_final (CONST xml_take_text (\<lambda>p. e)))"
  "_xml_block (_xml_cons (_xml_take_int p) (_xml_final e))"
  \<rightleftharpoons> "_xml_block (_xml_final (CONST xml_take_int (\<lambda>p. e)))"
  "_xml_block (_xml_cons (_xml_take_nat p) (_xml_final e))"
  \<rightleftharpoons> "_xml_block (_xml_final (CONST xml_take_nat (\<lambda>p. e)))"
  "_xml_block (_xml_cons (_xml_take_att p x) (_xml_final e))"
  \<rightleftharpoons> "_xml_block (_xml_final (CONST xml_take_attribute x (\<lambda>p. e)))"
  "_xml_block (_xml_cons (_xml_take_att_optional p x) (_xml_final e))"
  \<rightleftharpoons> "_xml_block (_xml_final (CONST xml_take_attribute_optional x (\<lambda>p. e)))"
  "_xml_block (_xml_cons (_xml_take_att_default p d x) (_xml_final e))"
  \<rightleftharpoons> "_xml_block (_xml_final (CONST xml_take_attribute_default d x (\<lambda>p. e)))"
  "_xml_block (_xml_cons (_xml_take_optional p x) (_xml_final e))"
  \<rightleftharpoons> "_xml_block (_xml_final (CONST xml_take_optional x (\<lambda>p. e)))"
  "_xml_block (_xml_cons (_xml_take_default p d x) (_xml_final e))"
  \<rightleftharpoons> "_xml_block (_xml_final (CONST xml_take_default d x (\<lambda>p. e)))"
  "_xml_block (_xml_cons (_xml_take_all p x) (_xml_final e))"
  \<rightleftharpoons> "_xml_block (_xml_final (CONST xml_take_many 0 \<infinity> x (\<lambda>p. e)))"
  "_xml_block (_xml_cons (_xml_take_many p minOccurs maxOccurs x) (_xml_final e))"
  \<rightleftharpoons> "_xml_block (_xml_final (CONST xml_take_many minOccurs maxOccurs x (\<lambda>p. e)))"
  "_xml_block (_xml_cons (_xml_let p t) bs)"
  \<rightleftharpoons> "let p = t in _xml_block bs"
  "_xml_block (_xml_cons b (_xml_cons c cs))"
  \<rightleftharpoons> "_xml_block (_xml_cons b (_xml_final (_xml_block (_xml_cons c cs))))"
  "_xml_cons (_xml_let p t) (_xml_final s)"
  \<rightleftharpoons> "_xml_final (let p = t in s)"
  "_xml_block (_xml_final e)" \<rightharpoonup> "e"
  "_xml_do t e" \<rightleftharpoons> "CONST xml_do t (_xml_block e)"

fun xml_error_to_string where
  "xml_error_to_string (Fatal e) = String.explode (STR ''Fatal: '' + e)" 
| "xml_error_to_string (TagMismatch e) = String.explode (STR ''tag mismatch: '' + default_showsl_list showsl_lit e (STR ''''))" 

definition parse_xml :: "'a xmlt \<Rightarrow> xml \<Rightarrow> string +\<^sub>\<bottom> 'a"
  where "parse_xml p xml \<equiv>
    bind2 (xml_take p xml_return ([xml],[],False,[],[])) 
      (Left o xml_error_to_string) Right"

(*BEGIN: special chars*)
subsection \<open>Handling of special characters in text\<close>

definition "special_map = map_of [
  (''quot'', ''\"''), (''#34'', ''\"''), \<comment> \<open>double quotation mark\<close>
  (''amp'', ''&''), (''#38'', ''&''), \<comment> \<open>ampersand\<close>
  (''apos'', [CHR 0x27]), (''#39'', [CHR 0x27]), \<comment> \<open>single quotes\<close>
  (''lt'', ''<''), (''#60'', ''<''), \<comment> \<open>less-than sign\<close>
  (''gt'', ''>''), (''#62'', ''>'') \<comment> \<open>greater-than sign\<close>
]"

fun extract_special
  where
    "extract_special acc [] = None"
  | "extract_special acc (x # xs) =
    (if x = CHR '';'' then map_option (\<lambda>s. (s, xs)) (special_map (rev acc))
    else extract_special (x#acc) xs)"

lemma extract_special_length [termination_simp]:
  assumes "extract_special acc xs = Some (y, ys)"
  shows "length ys < length xs"
  using assms by (induct acc xs rule: extract_special.induct) (auto split: if_splits)

fun normalize_special
  where
    "normalize_special [] = []"
  | "normalize_special (x # xs) =
      (if x = CHR ''&'' then
        (case extract_special [] xs of
          None \<Rightarrow> ''&'' @ normalize_special xs
        | Some (spec, ys) \<Rightarrow> spec @ normalize_special ys)
      else x # normalize_special xs)"

fun map_xml_text :: "(string \<Rightarrow> string) \<Rightarrow> xml \<Rightarrow> xml"
  where
    "map_xml_text f (XML t as cs) = XML t as (map (map_xml_text f) cs)"
  | "map_xml_text f (XML_text txt) = XML_text (f txt)"
    (*END: special chars*)

definition parse_xml_string :: "'a xmlt \<Rightarrow> string \<Rightarrow> string +\<^sub>\<bottom> 'a"
  where
    "parse_xml_string p str \<equiv> case doc_of_string str of
    Inl err \<Rightarrow> Left err
  | Inr (XMLDOC header xml) \<Rightarrow> parse_xml p (map_xml_text normalize_special xml)"


subsection \<open>For Terminating Parsers\<close>

(*TODO: replace the default size of xml *)
primrec size_xml
  where "size_xml (XML_text str) = size str"
  |   "size_xml (XML tag atts xmls) = 1 + size tag + (\<Sum>xml \<leftarrow> xmls. size_xml xml)"

abbreviation "size_xml_state \<equiv> size_xml \<circ> fst"
abbreviation "size_xmls_state x \<equiv> (\<Sum>xml \<leftarrow> fst x. size_xml xml)"

lemma size_xml_nth [dest]: "i < length xmls \<Longrightarrow> size_xml (xmls!i) \<le> sum_list (map size_xml xmls)"
  using elem_le_sum_list[of _ "map Xmlt.size_xml _", unfolded length_map] by auto

lemma xml_or_cong[fundef_cong]:
  assumes "\<And>info. p (fst x, info) = p' (fst x, info)"
    and "\<And>info. q (fst x, info) = q' (fst x, info)"
    and "x = x'"
  shows "(p XMLor q) x = (p' XMLor q') x'"
  using assms
  by (cases x, auto simp: xml_or_def intro!: Option.bind_cong split:sum.split xml_error.split)

lemma xml_do_cong[fundef_cong]:
  fixes p :: "'a xmlst"
  assumes "\<And>tag' atts xmls info. fst x = XML tag' atts xmls \<Longrightarrow> String.explode tag = tag' \<Longrightarrow> p (xmls,atts,info) = p' (xmls,atts,info)"
    and "x = x'"
  shows "xml_do tag p x = xml_do tag p' x'"
  using assms by (cases x, auto simp: xml_do_def split: xml.split)

lemma xml_take_cong[fundef_cong]:
  fixes p :: "'a xmlt" and q :: "'a \<Rightarrow> 'b xmlst"
  assumes "\<And>a as info. fst x = a#as \<Longrightarrow> p (a, info) = p' (a, info)"
    and "\<And>a as ret info info'. x' = (a#as,info) \<Longrightarrow> q ret (as, info') = q' ret (as, info')"
    and "\<And>info. p (XML [] [] [], info) = p' (XML [] [] [], info)"
    and "x = x'"
  shows "xml_take p q x = xml_take p' q' x'"
  using assms by (cases x, auto simp: xml_take_def intro!: Option.bind_cong split: list.split sum.split)

lemma xml_take_many_cong[fundef_cong]:
  fixes p :: "'a xmlt" and q :: "'a list \<Rightarrow> 'b xmlst"
  assumes p: "\<And>n info. n < length (fst x) \<Longrightarrow> p (fst x' ! n, info) = p' (fst x' ! n, info)"
    and err: "\<And>info. p (XML [] [] [], info) = p' (XML [] [] [], info)"
    and q: "\<And>ret n info. q ret (drop n (fst x'), info) = q' ret (drop n (fst x'), info)"
    and xx': "x = x'"
  shows "xml_take_many_sub ret minOccurs maxOccurs p q x = xml_take_many_sub ret minOccurs maxOccurs p' q' x'"
proof-
  obtain as b where x: "x = (as,b)" by (cases x, auto)
  show ?thesis
  proof (insert p q, fold xx', unfold x, induct as arbitrary: b minOccurs maxOccurs ret)
    case Nil
    with err show ?case by (cases b, auto intro!: Option.bind_cong)
  next
    case (Cons a as)
    from Cons(2,3)[where n=0] Cons(2,3)[where n="Suc n" for n]
    show ?case by (cases b, auto intro!: bind2_cong Cons(1) split: sum.split xml_error.split)
  qed
qed

lemma xml_take_optional_cong[fundef_cong]:
  fixes p :: "'a xmlt" and q :: "'a option \<Rightarrow> 'b xmlst"
  assumes "\<And>a as info. fst x = a # as \<Longrightarrow> p (a, info) = p' (a, info)"
    and "\<And>a as ret info. fst x = a # as \<Longrightarrow> q (Some ret) (as, info) = q' (Some ret) (as, info)"
    and "\<And>info. q None (fst x', info) = q' None (fst x', info)"
    and xx': "x = x'"
  shows "xml_take_optional p q x = xml_take_optional p' q' x'"
  using assms by (cases x', auto simp: xml_take_optional_def split: list.split sum.split xml_error.split intro!: bind2_cong)

lemma xml_take_default_cong[fundef_cong]:
  fixes p :: "'a xmlt" and q :: "'a \<Rightarrow> 'b xmlst"
  assumes "\<And>a as info. fst x = a # as \<Longrightarrow> p (a, info) = p' (a, info)"
    and "\<And>a as ret info. fst x = a # as \<Longrightarrow> q ret (as, info) = q' ret (as, info)"
    and "\<And>info. q d (fst x', info) = q' d (fst x', info)"
    and xx': "x = x'"
  shows "xml_take_default d p q x = xml_take_default d p' q' x'"
  using assms by (cases x', auto simp: xml_take_default_def split: list.split sum.split xml_error.split intro!: bind2_cong)


lemma xml_change_cong[fundef_cong]:
  assumes "x = x'"
    and "p x' = p' x'"
    and "\<And>ret y. p x = Right ret \<Longrightarrow> q ret y = q' ret y"
  shows "xml_change p q x = xml_change p' q' x'"
  using assms by (cases x', auto simp: xml_change_def split: option.split sum.split intro!: bind2_cong)


lemma if_cong_applied[fundef_cong]:
  "b = c \<Longrightarrow>
   (c \<Longrightarrow> x z = u w) \<Longrightarrow>
   (\<not> c \<Longrightarrow> y z = v w) \<Longrightarrow>
   z = w \<Longrightarrow>
   (if b then x else y) z = (if c then u else v) w"
  by auto

lemma option_case_cong[fundef_cong]:
  "option = option' \<Longrightarrow>
    (option' = None \<Longrightarrow> f1 z = g1 w) \<Longrightarrow>
    (\<And>x2. option' = Some x2 \<Longrightarrow> f2 x2 z = g2 x2 w) \<Longrightarrow>
    z = w \<Longrightarrow>
    (case option of None \<Rightarrow> f1 | Some x2 \<Rightarrow> f2 x2) z = (case option' of None \<Rightarrow> g1 | Some x2 \<Rightarrow> g2 x2) w"
  by (cases option, auto)

lemma sum_case_cong[fundef_cong]:
  "s = ss \<Longrightarrow>
  (\<And>x1. ss = Inl x1 \<Longrightarrow> f1 x1 z = g1 x1 w) \<Longrightarrow>
  (\<And>x2. ss = Inr x2 \<Longrightarrow> f2 x2 z = g2 x2 w) \<Longrightarrow>
  z = w \<Longrightarrow>
  (case s of Inl x1 \<Rightarrow> f1 x1 | Inr x2 \<Rightarrow> f2 x2) z = (case ss of Inl x1 \<Rightarrow> g1 x1 | Inr x2 \<Rightarrow> g2 x2) w"
  by (cases s, auto)

lemma prod_case_cong[fundef_cong]: "p = pp \<Longrightarrow>
  (\<And>x1 x2. pp = (x1, x2) \<Longrightarrow> f x1 x2 z = g x1 x2 w) \<Longrightarrow>
  (case p of (x1, x2) \<Rightarrow> f x1 x2) z = (case pp of (x1, x2) \<Rightarrow> g x1 x2) w"
  by (auto split: prod.split)

text \<open>Mononicity rules of combinators for partial-function command.\<close>

lemma bind2_mono [partial_function_mono]:
  assumes p0: "mono_sum_bot p0" 
  assumes p1: "\<And>y. mono_sum_bot (p1 y)" 
  assumes p2: "\<And>y. mono_sum_bot (p2 y)" 
  shows "mono_sum_bot (\<lambda>g. bind2 (p0 g) (\<lambda>y. p1 y g) (\<lambda>y. p2 y g))"
proof (rule monotoneI)
  fix f g :: "'a \<Rightarrow> 'b +\<^sub>\<bottom> 'c" 
  assume fg: "fun_ord sum_bot_ord f g" 
  with p0 have "sum_bot_ord (p0 f) (p0 g)" by (rule monotoneD[of _ _ _ f g])
  then have "sum_bot_ord 
    (bind2 (p0 f) (\<lambda> y. p1 y f) (\<lambda> y. p2 y f))
    (bind2 (p0 g) (\<lambda> y. p1 y f) (\<lambda> y. p2 y f))" 
    unfolding flat_ord_def bind2_def by auto
  also from p1 have "\<And> y'. sum_bot_ord (p1 y' f) (p1 y' g)" 
    by (rule monotoneD) (rule fg)
  then have "sum_bot_ord 
    (bind2 (p0 g) (\<lambda> y. p1 y f) (\<lambda> y. p2 y f))
    (bind2 (p0 g) (\<lambda> y. p1 y g) (\<lambda> y. p2 y f))"
    unfolding flat_ord_def by (cases "p0 g") (auto simp: bind2_def)
  also (sum_bot.leq_trans)
  from p2 have "\<And> y'. sum_bot_ord (p2 y' f) (p2 y' g)" 
    by (rule monotoneD) (rule fg)
  then have "sum_bot_ord 
    (bind2 (p0 g) (\<lambda> y. p1 y g) (\<lambda> y. p2 y f))
    (bind2 (p0 g) (\<lambda> y. p1 y g) (\<lambda> y. p2 y g))"
    unfolding flat_ord_def by (cases "p0 g") (auto simp: bind2_def)
  finally (sum_bot.leq_trans)
  show "sum_bot_ord (bind2 (p0 f) (\<lambda>y. p1 y f) (\<lambda>y. p2 y f))
            (bind2 (p0 g) (\<lambda>ya. p1 ya g) (\<lambda>ya. p2 ya g))" .
qed

lemma xml_or_mono [partial_function_mono]:
  assumes p1: "\<And>y. mono_sum_bot (p1 y)" 
  assumes p2: "\<And>y. mono_sum_bot (p2 y)" 
  shows "mono_sum_bot (\<lambda>g. xml_or (\<lambda>y. p1 y g) (\<lambda>y. p2 y g) x)"
  using p1 unfolding xml_or_def
  by (cases x, auto simp: xml_or_def intro!: partial_function_mono,
      intro monotoneI, auto split: xml_error.splits simp: sum_bot.leq_refl dest: monotoneD[OF p2])

lemma xml_do_mono [partial_function_mono]:
  assumes p1: "\<And>y. mono_sum_bot (p1 y)" 
  shows "mono_sum_bot (\<lambda>g. xml_do t (\<lambda>y. p1 y g) x)" 
  by (cases x, cases "fst x") (auto simp: xml_do_def intro!: partial_function_mono p1)

lemma xml_take_mono [partial_function_mono]:
  assumes p1: "\<And>y. mono_sum_bot (p1 y)" 
  assumes p2: "\<And>x z. mono_sum_bot (\<lambda> y. p2 z x y)"  
  shows "mono_sum_bot (\<lambda>g. xml_take (\<lambda>y. p1 y g) (\<lambda> x y. p2 x y g) x)"
proof (cases x)
  case (fields a b c d e)
  show ?thesis unfolding xml_take_def fields split
    by (cases a, auto intro!: partial_function_mono p2 p1)
qed

lemma xml_take_default_mono [partial_function_mono]:
  assumes p1: "\<And>y. mono_sum_bot (p1 y)" 
  assumes p2: "\<And>x z. mono_sum_bot (\<lambda> y. p2 z x y)"  
  shows "mono_sum_bot (\<lambda>g. xml_take_default a (\<lambda>y. p1 y g) (\<lambda> x y. p2 x y g) x)"
proof (cases x)
  case (fields a b c d e)
  show ?thesis unfolding xml_take_default_def fields split
    by (cases a, auto intro!: partial_function_mono p2 p1, intro monotoneI,
        auto split: xml_error.splits simp: sum_bot.leq_refl dest: monotoneD[OF p2])
qed

lemma xml_take_optional_mono [partial_function_mono]:
  assumes p1: "\<And>y. mono_sum_bot (p1 y)" 
  assumes p2: "\<And>x z. mono_sum_bot (\<lambda> y. p2 z x y)"  
  shows "mono_sum_bot (\<lambda>g. xml_take_optional (\<lambda>y. p1 y g) (\<lambda> x y. p2 x y g) x)" 
proof (cases x)
  case (fields a b c d e)
  show ?thesis unfolding xml_take_optional_def fields split
    by (cases a, auto intro!: partial_function_mono p2 p1, intro monotoneI,
        auto split: xml_error.splits simp: sum_bot.leq_refl dest: monotoneD[OF p2])
qed

lemma xml_change_mono [partial_function_mono]:
  assumes p1: "\<And>y. mono_sum_bot (p1 y)" 
  assumes p2: "\<And>x z. mono_sum_bot (\<lambda> y. p2 z x y)"  
  shows "mono_sum_bot (\<lambda>g. xml_change (\<lambda>y. p1 y g) (\<lambda> x y. p2 x y g) x)" 
  unfolding xml_change_def by (intro partial_function_mono p1, cases x, auto intro: p2)

lemma xml_take_many_sub_mono [partial_function_mono]:
  assumes p1: "\<And>y. mono_sum_bot (p1 y)" 
  assumes p2: "\<And>x z. mono_sum_bot (\<lambda> y. p2 z x y)"  
  shows "mono_sum_bot (\<lambda>g. xml_take_many_sub a b c (\<lambda>y. p1 y g) (\<lambda> x y. p2 x y g) x)" 
proof -
  obtain xs atts allow cands rest where x: "x = (xs, atts, allow, cands, rest)" by (cases x)
  show ?thesis unfolding x 
  proof (induct xs arbitrary: a b c atts allow rest cands)
    case Nil
    show ?case by (auto intro!: partial_function_mono p1 p2)
  next
    case (Cons x xs)
    show ?case unfolding xml_take_many_sub.simps
      by (auto intro!: partial_function_mono p2 p1 Cons, intro monotoneI,
          auto split: xml_error.splits simp: sum_bot.leq_refl dest: monotoneD[OF p2])
  qed
qed

partial_function (sum_bot) xml_foldl :: "('a \<Rightarrow> 'b xmlt) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a xmlst" where
  [code]: "xml_foldl p f a xs = (case xs of ([],_) \<Rightarrow> Right a
     | _ \<Rightarrow> xml_take (p a) (\<lambda> b. xml_foldl p f (f a b)) xs)" 

end
