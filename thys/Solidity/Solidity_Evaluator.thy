section\<open> Solidty Evaluator and Code Generator Setup\<close>

theory
  Solidity_Evaluator
imports
  Solidity_Main
  "HOL-Library.Code_Target_Numeral"
  "HOL-Library.Sublist"
  "HOL-Library.Finite_Map"
begin

paragraph\<open>Generalized Unit Tests\<close>

lemma  "createSInt b8 500 = STR ''-12''" by eval

lemma "STR ''-92134039538802366542421159375273829975'' 
      = createSInt b128 45648483135649456465465452123894894554654654654654646999465"
  by eval

lemma "STR ''-128'' = createSInt b8 (-128)" by eval

lemma "STR ''244'' = createUInt b8 500" by eval

lemma "STR ''220443428915524155977936330922349307608'' 
      = createUInt b128 4564848313564945646546545212389489455465465465465464699946544654654654654168"
  by eval

lemma "less (TUInt b144) (TSInt b160) (STR ''5'') (STR ''8'') = Some(STR ''True'', TBool) "
  by eval

subsection\<open>Code Generator Setup and Local Tests\<close>

subsubsection\<open>Utils\<close>

definition EMPTY::"String.literal" where "EMPTY = STR ''''"

definition FAILURE::"String.literal" where "FAILURE = STR ''Failure''"

fun intersperse :: "String.literal \<Rightarrow> String.literal list \<Rightarrow> String.literal" where
  "intersperse s [] = EMPTY"
| "intersperse s [x] = x"
| "intersperse s (x # xs) = x + s + intersperse s xs"

definition splitAt::"nat \<Rightarrow> String.literal \<Rightarrow> String.literal \<times> String.literal" where
"splitAt n xs = (String.implode(take n (String.explode xs)), String.implode(drop n (String.explode xs)))"

fun splitOn':: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list list" where  
   "splitOn' x [] acc = [rev acc]"
 | "splitOn' x (y#ys) acc = (if x = y then (rev acc)#(splitOn' x ys [])
                                      else splitOn' x ys (y#acc))"

fun splitOn::"'a  \<Rightarrow> 'a list \<Rightarrow> 'a list list" where
"splitOn x xs = splitOn' x xs []"

definition isSuffixOf::"String.literal \<Rightarrow> String.literal \<Rightarrow> bool" where
"isSuffixOf s x = suffix (String.explode s) (String.explode x)"

definition tolist :: "location \<Rightarrow> String.literal list" where 
"tolist s = map String.implode (splitOn (CHR ''.'') (String.explode s))"

abbreviation convert :: "location \<Rightarrow> location"
  where "convert loc \<equiv> (if loc= STR ''True'' then STR ''true'' else
    if loc=STR ''False'' then STR ''false'' else loc)"

definition \<open>sorted_list_of_set' \<equiv> map_fun id id (folding_on.F insort [])\<close>

lemma sorted_list_of_fset'_def': \<open>sorted_list_of_set' = sorted_list_of_set\<close>
  apply(rule ext)
  by (simp add: sorted_list_of_set'_def sorted_list_of_set_def sorted_key_list_of_set_def)

lemma sorted_list_of_set_sort_remdups' [code]:
  \<open>sorted_list_of_set' (set xs) = sort (remdups xs)\<close>
  using sorted_list_of_fset'_def' sorted_list_of_set_sort_remdups                      
  by metis

definition  locations_map :: "location \<Rightarrow> (location, 'v) fmap \<Rightarrow> location list" where
"locations_map loc = (filter (isSuffixOf ((STR ''.'')+loc))) \<circ>  sorted_list_of_set' \<circ> fset \<circ> fmdom"

definition  locations :: "location \<Rightarrow> 'v store \<Rightarrow> location list" where
"locations loc = locations_map loc \<circ> Mapping"

subsubsection\<open>Valuetypes\<close>

fun dump\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e\<^sub>t\<^sub>y\<^sub>p\<^sub>e\<^sub>s::"types \<Rightarrow> valuetype \<Rightarrow> String.literal" where
   "dump\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e\<^sub>t\<^sub>y\<^sub>p\<^sub>e\<^sub>s (TSInt _) n = n"
 | "dump\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e\<^sub>t\<^sub>y\<^sub>p\<^sub>e\<^sub>s (TUInt _) n = n"
 | "dump\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e\<^sub>t\<^sub>y\<^sub>p\<^sub>e\<^sub>s TBool b = (if b = (STR ''True'') then  STR ''true'' else STR ''false'')"
 | "dump\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e\<^sub>t\<^sub>y\<^sub>p\<^sub>e\<^sub>s TAddr ad = ad"

subsubsection\<open>Memory\<close>

datatype data\<^sub>M\<^sub>e\<^sub>m\<^sub>o\<^sub>r\<^sub>y = MArray "data\<^sub>M\<^sub>e\<^sub>m\<^sub>o\<^sub>r\<^sub>y list"
                   | MBool bool
                   | MInt int
                   | MAddress address

fun loadRec\<^sub>M\<^sub>e\<^sub>m\<^sub>o\<^sub>r\<^sub>y :: "location \<Rightarrow> data\<^sub>M\<^sub>e\<^sub>m\<^sub>o\<^sub>r\<^sub>y \<Rightarrow> memoryT \<Rightarrow> memoryT" and
        iterateM :: "location \<Rightarrow> memoryT \<times> nat \<Rightarrow> data\<^sub>M\<^sub>e\<^sub>m\<^sub>o\<^sub>r\<^sub>y \<Rightarrow> memoryT \<times> nat" where
  "loadRec\<^sub>M\<^sub>e\<^sub>m\<^sub>o\<^sub>r\<^sub>y loc (MArray dat) mem = fst (foldl (iterateM loc) (updateStore loc (MPointer loc) mem,0) dat)"
| "loadRec\<^sub>M\<^sub>e\<^sub>m\<^sub>o\<^sub>r\<^sub>y loc (MBool b) mem = updateStore loc ((MValue \<circ> ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l) b) mem "
| "loadRec\<^sub>M\<^sub>e\<^sub>m\<^sub>o\<^sub>r\<^sub>y loc (MInt i) mem = updateStore loc ((MValue \<circ> ShowL\<^sub>i\<^sub>n\<^sub>t) i) mem "
| "loadRec\<^sub>M\<^sub>e\<^sub>m\<^sub>o\<^sub>r\<^sub>y loc (MAddress ad) mem = updateStore loc (MValue ad) mem"
| "iterateM loc (mem,x) d = (loadRec\<^sub>M\<^sub>e\<^sub>m\<^sub>o\<^sub>r\<^sub>y (hash loc (ShowL\<^sub>n\<^sub>a\<^sub>t x)) d mem, Suc x)"

definition load\<^sub>M\<^sub>e\<^sub>m\<^sub>o\<^sub>r\<^sub>y :: "data\<^sub>M\<^sub>e\<^sub>m\<^sub>o\<^sub>r\<^sub>y list \<Rightarrow> memoryT \<Rightarrow> memoryT" where
"load\<^sub>M\<^sub>e\<^sub>m\<^sub>o\<^sub>r\<^sub>y dat mem = (let loc   = ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem);
                         (m, _) = foldl (iterateM loc) (mem, 0) dat
                       in (snd \<circ> allocate) m)"
                          
fun dumprec\<^sub>M\<^sub>e\<^sub>m\<^sub>o\<^sub>r\<^sub>y:: "location \<Rightarrow> mtypes \<Rightarrow> memoryT \<Rightarrow> String.literal \<Rightarrow> String.literal \<Rightarrow> String.literal" where
"dumprec\<^sub>M\<^sub>e\<^sub>m\<^sub>o\<^sub>r\<^sub>y loc tp mem ls str =
  (case accessStore loc mem of
    Some (MPointer l) \<Rightarrow>
      (case tp of
        (MTArray x t) \<Rightarrow> iter (\<lambda>i str' . dumprec\<^sub>M\<^sub>e\<^sub>m\<^sub>o\<^sub>r\<^sub>y ((hash l o ShowL\<^sub>n\<^sub>a\<^sub>t) i) t mem 
                              (ls + (STR ''['') + (ShowL\<^sub>n\<^sub>a\<^sub>t i) + (STR '']'')) str') str x
                  | _ \<Rightarrow> FAILURE)
  | Some (MValue v) \<Rightarrow>
      (case tp of
        MTValue t \<Rightarrow> str + ls + (STR ''=='') + dump\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e\<^sub>t\<^sub>y\<^sub>p\<^sub>e\<^sub>s t v + (STR ''\<newline>'')
              | _ \<Rightarrow> FAILURE)
  | None \<Rightarrow> FAILURE)"

definition dump\<^sub>M\<^sub>e\<^sub>m\<^sub>o\<^sub>r\<^sub>y :: "location \<Rightarrow> nat \<Rightarrow> mtypes \<Rightarrow> memoryT \<Rightarrow> String.literal \<Rightarrow>String.literal \<Rightarrow>String.literal" where
"dump\<^sub>M\<^sub>e\<^sub>m\<^sub>o\<^sub>r\<^sub>y loc x t mem ls str = iter (\<lambda>i. dumprec\<^sub>M\<^sub>e\<^sub>m\<^sub>o\<^sub>r\<^sub>y ((hash loc (ShowL\<^sub>n\<^sub>a\<^sub>t i))) t mem (ls + STR ''['' + (ShowL\<^sub>n\<^sub>a\<^sub>t i + STR '']''))) str x"

subsubsection\<open>Storage\<close>

datatype data\<^sub>S\<^sub>t\<^sub>o\<^sub>r\<^sub>a\<^sub>g\<^sub>e =
    SArray "data\<^sub>S\<^sub>t\<^sub>o\<^sub>r\<^sub>a\<^sub>g\<^sub>e list"
  | SMap "(String.literal \<times> data\<^sub>S\<^sub>t\<^sub>o\<^sub>r\<^sub>a\<^sub>g\<^sub>e) list"
  | SBool bool
  | SInt int
  | SAddress address

fun go\<^sub>S\<^sub>t\<^sub>o\<^sub>r\<^sub>a\<^sub>g\<^sub>e :: "location \<Rightarrow> (String.literal \<times>  stypes) \<Rightarrow> (String.literal \<times> stypes)" where
  "go\<^sub>S\<^sub>t\<^sub>o\<^sub>r\<^sub>a\<^sub>g\<^sub>e l (s, STArray _ t) = (s + (STR ''['') + (convert l) + (STR '']''), t)"
| "go\<^sub>S\<^sub>t\<^sub>o\<^sub>r\<^sub>a\<^sub>g\<^sub>e l (s, STMap _ t) = (s + (STR ''['') + (convert l) + (STR '']''), t)"
| "go\<^sub>S\<^sub>t\<^sub>o\<^sub>r\<^sub>a\<^sub>g\<^sub>e l (s, STValue t) = (s + (STR ''['') + (convert l) + (STR '']''), STValue t)"

fun dumpSingle\<^sub>S\<^sub>t\<^sub>o\<^sub>r\<^sub>a\<^sub>g\<^sub>e :: "storageT \<Rightarrow> String.literal \<Rightarrow> stypes \<Rightarrow> (location \<times> location) \<Rightarrow> String.literal \<Rightarrow> String.literal" where
"dumpSingle\<^sub>S\<^sub>t\<^sub>o\<^sub>r\<^sub>a\<^sub>g\<^sub>e sto id' tp (loc,l) str =
    (case foldr go\<^sub>S\<^sub>t\<^sub>o\<^sub>r\<^sub>a\<^sub>g\<^sub>e (tolist loc) (str + id', tp) of
      (s, STValue t) \<Rightarrow>
        (case sto $$ (loc + l) of
           Some v \<Rightarrow> s + (STR ''=='') + dump\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e\<^sub>t\<^sub>y\<^sub>p\<^sub>e\<^sub>s t v
         | None \<Rightarrow> FAILURE)
     | _ \<Rightarrow> FAILURE)"

definition iterate where
"iterate loc t id' sto s l = dumpSingle\<^sub>S\<^sub>t\<^sub>o\<^sub>r\<^sub>a\<^sub>g\<^sub>e sto id' t (splitAt (length (String.explode l) - length (String.explode loc) - 1) l) s + (STR ''\<newline>'')"

fun dump\<^sub>S\<^sub>t\<^sub>o\<^sub>r\<^sub>a\<^sub>g\<^sub>e ::  "storageT \<Rightarrow> location \<Rightarrow> String.literal \<Rightarrow> stypes \<Rightarrow> String.literal \<Rightarrow> String.literal" where
  "dump\<^sub>S\<^sub>t\<^sub>o\<^sub>r\<^sub>a\<^sub>g\<^sub>e sto loc id' (STArray _ t) str = foldl (iterate loc t id' sto) str (locations_map loc sto)"
| "dump\<^sub>S\<^sub>t\<^sub>o\<^sub>r\<^sub>a\<^sub>g\<^sub>e sto loc id' (STMap _ t) str = foldl (iterate loc t id' sto) str (locations_map loc sto)"
| "dump\<^sub>S\<^sub>t\<^sub>o\<^sub>r\<^sub>a\<^sub>g\<^sub>e sto loc id' (STValue t) str =
    (case sto $$ loc of
      Some v \<Rightarrow> str + id' + (STR ''=='') + dump\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e\<^sub>t\<^sub>y\<^sub>p\<^sub>e\<^sub>s t v + (STR ''\<newline>'')
    | _ \<Rightarrow> str)"

fun loadRec\<^sub>S\<^sub>t\<^sub>o\<^sub>r\<^sub>a\<^sub>g\<^sub>e :: "location \<Rightarrow> data\<^sub>S\<^sub>t\<^sub>o\<^sub>r\<^sub>a\<^sub>g\<^sub>e \<Rightarrow> storageT \<Rightarrow> storageT" and
    iterateSA :: "location \<Rightarrow> storageT \<times> nat \<Rightarrow> data\<^sub>S\<^sub>t\<^sub>o\<^sub>r\<^sub>a\<^sub>g\<^sub>e \<Rightarrow> storageT \<times> nat" and
    iterateSM :: "location \<Rightarrow> String.literal \<times> data\<^sub>S\<^sub>t\<^sub>o\<^sub>r\<^sub>a\<^sub>g\<^sub>e \<Rightarrow> storageT \<Rightarrow> storageT" where
  "loadRec\<^sub>S\<^sub>t\<^sub>o\<^sub>r\<^sub>a\<^sub>g\<^sub>e loc (SArray dat) sto = fst (foldl (iterateSA loc) (sto,0) dat)"
| "loadRec\<^sub>S\<^sub>t\<^sub>o\<^sub>r\<^sub>a\<^sub>g\<^sub>e loc (SMap dat) sto  = foldr (iterateSM loc) dat sto"
| "loadRec\<^sub>S\<^sub>t\<^sub>o\<^sub>r\<^sub>a\<^sub>g\<^sub>e loc (SBool b) sto = fmupd loc (ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l b) sto"
| "loadRec\<^sub>S\<^sub>t\<^sub>o\<^sub>r\<^sub>a\<^sub>g\<^sub>e loc (SInt i)  sto = fmupd loc (ShowL\<^sub>i\<^sub>n\<^sub>t i) sto"
| "loadRec\<^sub>S\<^sub>t\<^sub>o\<^sub>r\<^sub>a\<^sub>g\<^sub>e loc (SAddress ad) sto = fmupd loc ad sto"
| "iterateSA loc (s', x) d = (loadRec\<^sub>S\<^sub>t\<^sub>o\<^sub>r\<^sub>a\<^sub>g\<^sub>e (hash loc (ShowL\<^sub>n\<^sub>a\<^sub>t x)) d s', Suc x)"
| "iterateSM loc (k, v) s' = loadRec\<^sub>S\<^sub>t\<^sub>o\<^sub>r\<^sub>a\<^sub>g\<^sub>e (hash loc k) v s'"

subsubsection\<open>environment\<close>

datatype data\<^sub>E\<^sub>n\<^sub>v\<^sub>i\<^sub>r\<^sub>o\<^sub>n\<^sub>m\<^sub>e\<^sub>n\<^sub>t =
    Memarr "data\<^sub>M\<^sub>e\<^sub>m\<^sub>o\<^sub>r\<^sub>y list" |
    CDarr "data\<^sub>M\<^sub>e\<^sub>m\<^sub>o\<^sub>r\<^sub>y list" |
    Stoarr "data\<^sub>S\<^sub>t\<^sub>o\<^sub>r\<^sub>a\<^sub>g\<^sub>e list"|
    Stomap "(String.literal \<times> data\<^sub>S\<^sub>t\<^sub>o\<^sub>r\<^sub>a\<^sub>g\<^sub>e) list" |
    Stackbool bool |
    Stobool bool |
    Stackint int |
    Stoint int |
    Stackaddr address |
    Stoaddr address

fun astore :: "Identifier \<Rightarrow> type \<Rightarrow> valuetype \<Rightarrow> storageT * environment \<Rightarrow> storageT * environment"
  where "astore i t v (s, e) = (fmupd i v s, (updateEnv i t (Storeloc i) e))"

fun loadsimple\<^sub>E\<^sub>n\<^sub>v\<^sub>i\<^sub>r\<^sub>o\<^sub>n\<^sub>m\<^sub>e\<^sub>n\<^sub>t :: "(stack \<times> calldataT \<times> memoryT \<times> storageT \<times> environment) 
                    \<Rightarrow> (Identifier \<times> type \<times> data\<^sub>E\<^sub>n\<^sub>v\<^sub>i\<^sub>r\<^sub>o\<^sub>n\<^sub>m\<^sub>e\<^sub>n\<^sub>t) \<Rightarrow> (stack \<times> calldataT \<times> memoryT \<times> storageT \<times> environment)"
  where
"loadsimple\<^sub>E\<^sub>n\<^sub>v\<^sub>i\<^sub>r\<^sub>o\<^sub>n\<^sub>m\<^sub>e\<^sub>n\<^sub>t (k, c, m, s, e) (id', tp, d) = (case d of
    Stackbool b \<Rightarrow>
        let (k', e') = astack id' tp (KValue (ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l b)) (k, e)
        in (k', c, m, s, e')
  | Stobool b \<Rightarrow>
        let (s', e') = astore id' tp (ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l b) (s, e)
        in (k, c, m, s', e')
  |  Stackint n \<Rightarrow>
        let (k', e') = astack id' tp (KValue (ShowL\<^sub>i\<^sub>n\<^sub>t n)) (k, e)
        in (k', c, m, s, e')
  |  Stoint n \<Rightarrow>
        let (s', e') = astore id' tp (ShowL\<^sub>i\<^sub>n\<^sub>t n) (s, e)
        in (k, c, m, s', e')
  |  Stackaddr ad \<Rightarrow>
        let (k', e') = astack id' tp (KValue ad) (k, e)
        in (k', c, m, s, e')
  |  Stoaddr ad \<Rightarrow>
        let (s', e') = astore id' tp ad (s, e)
        in (k, c, m, s', e')
  |  CDarr a \<Rightarrow>
        let l = ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc c);
            c' = load\<^sub>M\<^sub>e\<^sub>m\<^sub>o\<^sub>r\<^sub>y a c;
            (k', e') = astack id' tp (KCDptr l) (k, e)
        in (k', c', m, s, e')
  |  Memarr a \<Rightarrow>
        let l = ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc m);
            m' = load\<^sub>M\<^sub>e\<^sub>m\<^sub>o\<^sub>r\<^sub>y a m;
            (k', e') = astack id' tp (KMemptr l) (k, e)
        in (k', c, m', s, e')
  |  Stoarr a \<Rightarrow>
        let s' = loadRec\<^sub>S\<^sub>t\<^sub>o\<^sub>r\<^sub>a\<^sub>g\<^sub>e id' (SArray a) s;
            e' = updateEnv id' tp (Storeloc id') e
        in (k, c, m, s', e')
  |  Stomap mp \<Rightarrow>
        let s' = loadRec\<^sub>S\<^sub>t\<^sub>o\<^sub>r\<^sub>a\<^sub>g\<^sub>e id' (SMap mp) s;
            e' = updateEnv id' tp (Storeloc id') e
        in (k, c, m, s', e')
)"

definition getValue\<^sub>E\<^sub>n\<^sub>v\<^sub>i\<^sub>r\<^sub>o\<^sub>n\<^sub>m\<^sub>e\<^sub>n\<^sub>t :: "stack \<Rightarrow> calldataT \<Rightarrow> memoryT \<Rightarrow> storageT \<Rightarrow> environment \<Rightarrow> Identifier \<Rightarrow> String.literal \<Rightarrow> String.literal"
  where 
"getValue\<^sub>E\<^sub>n\<^sub>v\<^sub>i\<^sub>r\<^sub>o\<^sub>n\<^sub>m\<^sub>e\<^sub>n\<^sub>t k c m s e i txt = (case fmlookup (Denvalue e) i of
    Some (tp, Stackloc l) \<Rightarrow> (case accessStore l k of
        Some (KValue v) \<Rightarrow> (case tp of
            Value t \<Rightarrow> (txt + i + (STR ''=='') + dump\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e\<^sub>t\<^sub>y\<^sub>p\<^sub>e\<^sub>s t v + (STR ''\<newline>''))
          |  _ \<Rightarrow> FAILURE)
      | Some (KCDptr p) \<Rightarrow> (case tp of
            Calldata (MTArray x t) \<Rightarrow> dump\<^sub>M\<^sub>e\<^sub>m\<^sub>o\<^sub>r\<^sub>y p x t c i txt
            | _ \<Rightarrow> FAILURE)
      | Some (KMemptr p) \<Rightarrow> (case tp of
            type.Memory (MTArray x t) \<Rightarrow> dump\<^sub>M\<^sub>e\<^sub>m\<^sub>o\<^sub>r\<^sub>y p x t m i txt
            | _ \<Rightarrow> FAILURE)
      | Some (KStoptr p) \<Rightarrow> (case tp of
            type.Storage t \<Rightarrow> dump\<^sub>S\<^sub>t\<^sub>o\<^sub>r\<^sub>a\<^sub>g\<^sub>e s p i t txt
            | _ \<Rightarrow> FAILURE))
   | Some (type.Storage t, Storeloc l) \<Rightarrow> dump\<^sub>S\<^sub>t\<^sub>o\<^sub>r\<^sub>a\<^sub>g\<^sub>e s l i t txt
   | _ \<Rightarrow> FAILURE
)"

definition dump\<^sub>E\<^sub>n\<^sub>v\<^sub>i\<^sub>r\<^sub>o\<^sub>n\<^sub>m\<^sub>e\<^sub>n\<^sub>t :: "stack  \<Rightarrow> calldataT \<Rightarrow> memoryT \<Rightarrow> storageT \<Rightarrow> environment \<Rightarrow> Identifier list \<Rightarrow> String.literal" 
  where "dump\<^sub>E\<^sub>n\<^sub>v\<^sub>i\<^sub>r\<^sub>o\<^sub>n\<^sub>m\<^sub>e\<^sub>n\<^sub>t k c m s e sl = foldr (getValue\<^sub>E\<^sub>n\<^sub>v\<^sub>i\<^sub>r\<^sub>o\<^sub>n\<^sub>m\<^sub>e\<^sub>n\<^sub>t k c m s e) sl EMPTY"

subsubsection\<open>accounts\<close>

fun load\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t\<^sub>s :: "accounts \<Rightarrow> (address \<times> balance \<times> atype \<times> nat) list \<Rightarrow> accounts" where 
   "load\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t\<^sub>s acc []             = acc"
 | "load\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t\<^sub>s acc ((ad, b, t, c)#as) = load\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t\<^sub>s (acc (ad:=\<lparr>Bal=b, Type=Some t, Contracts=c\<rparr>)) as"

fun dumpStorage::"storageT \<Rightarrow> (Identifier \<times> member) \<Rightarrow> String.literal" where
  "dumpStorage s (i, Var x) = dump\<^sub>S\<^sub>t\<^sub>o\<^sub>r\<^sub>a\<^sub>g\<^sub>e s i i x EMPTY"
| "dumpStorage s (i, Function x) = FAILURE"
| "dumpStorage s (i, Method x) = FAILURE"

fun dumpMembers :: "atype option \<Rightarrow> environment\<^sub>p \<Rightarrow> storageT \<Rightarrow> String.literal" where
  "dumpMembers None ep s = FAILURE"
| "dumpMembers (Some EOA) _ _ = STR ''EOA''"
| "dumpMembers (Some (atype.Contract name)) ep s =
    (case ep $$ name of
      Some (ct, _) \<Rightarrow> name + STR ''('' + (intersperse (STR '','') (map (dumpStorage s) (filter (is_Var \<circ> snd) (sorted_list_of_fmap ct)))) + STR '')''
    | None \<Rightarrow> FAILURE)"

(*
  The first parameter is just to guarantee termination
*)
fun dump\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t :: "nat \<Rightarrow> environment\<^sub>p \<Rightarrow> state \<Rightarrow> address \<Rightarrow> String.literal"
  where "dump\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t 0 _ _ _ = FAILURE"
  | "dump\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t (Suc c) ep st a = a + STR '': '' +
        STR ''balance=='' + Bal (Accounts st a) +
        STR '' - '' + dumpMembers (Type (Accounts st a)) ep (Storage st a) +
        iter (\<lambda>x s. s + STR ''\<newline>'' + dump\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t c ep st (hash_version a (ShowL\<^sub>n\<^sub>a\<^sub>t x))) EMPTY ((Contracts (Accounts st a)))"

definition dump\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t\<^sub>s :: "environment\<^sub>p \<Rightarrow> state \<Rightarrow> address list \<Rightarrow> String.literal"
  where "dump\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t\<^sub>s ep st al = intersperse (STR ''\<newline>'') (map (dump\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t 1000 ep st) al)"

definition init\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t::"(address \<times> balance \<times> atype \<times> nat) list \<Rightarrow> accounts" where 
  "init\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t = load\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t\<^sub>s emptyAccount"

type_synonym data\<^sub>P = "(Identifier \<times> member) list \<times> ((Identifier \<times> type) list \<times> s) \<times> s"

fun loadProc::"Identifier \<Rightarrow> data\<^sub>P \<Rightarrow> environment\<^sub>p \<Rightarrow> environment\<^sub>p"
  where "loadProc i (xs, fb) = fmupd i (fmap_of_list xs, fb)"

subsection\<open>Test Setup\<close>

definition(in statement_with_gas) eval::"gas \<Rightarrow> s \<Rightarrow> address \<Rightarrow> Identifier \<Rightarrow> address \<Rightarrow> valuetype \<Rightarrow> (address \<times> balance \<times> atype \<times> nat) list 
                 \<Rightarrow> (String.literal \<times> type \<times> data\<^sub>E\<^sub>n\<^sub>v\<^sub>i\<^sub>r\<^sub>o\<^sub>n\<^sub>m\<^sub>e\<^sub>n\<^sub>t) list
          \<Rightarrow> String.literal"
  where "eval g stm addr name adest aval acc dat
        = (let (k,c,m,s,e) = foldl loadsimple\<^sub>E\<^sub>n\<^sub>v\<^sub>i\<^sub>r\<^sub>o\<^sub>n\<^sub>m\<^sub>e\<^sub>n\<^sub>t (emptyStore, emptyTypedStore, emptyTypedStore, fmempty, emptyEnv addr name adest aval) dat;
               a         = init\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t acc;
               s'        = emptyStorage (addr := s);
               z         = \<lparr>Accounts=a,Stack=k,Memory=m,Storage=s',Gas=g\<rparr> 
           in (
             case (stmt stm e c z) of
              Normal ((), z') \<Rightarrow> (dump\<^sub>E\<^sub>n\<^sub>v\<^sub>i\<^sub>r\<^sub>o\<^sub>n\<^sub>m\<^sub>e\<^sub>n\<^sub>t (Stack z') c (Memory z') (Storage z' addr) e (map (\<lambda> (a,b,c). a) dat))
                             + (dump\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t\<^sub>s ep z' (map fst acc))
             | Exception Err   \<Rightarrow> STR ''Exception''
             | Exception gas   \<Rightarrow> STR ''OutOfGas''))"

global_interpretation soliditytest0: statement_with_gas costs_ex "fmap_of_list []" costs_min
  defines stmt0 = "soliditytest0.stmt"
      and lexp0 = soliditytest0.lexp 
      and expr0 = soliditytest0.expr
      and ssel0 = soliditytest0.ssel
      and rexp0 = soliditytest0.rexp
      and msel0 = soliditytest0.msel
      and load0 = soliditytest0.load
      and eval0 = soliditytest0.eval
  by unfold_locales auto

lemma "eval0 1000
            SKIP 
            (STR ''089Be5381FcEa58aF334101414c04F993947C733'')
            EMPTY
            EMPTY
            (STR ''0'')
            [(STR ''089Be5381FcEa58aF334101414c04F993947C733'', STR ''100'', EOA, 0), (STR ''115f6e2F70210C14f7DB1AC69737a3CC78435d49'', STR ''100'', EOA, 0)] 
            [(STR ''v1'', (Value TBool, Stackbool True))]
     = STR ''v1==true\<newline>089Be5381FcEa58aF334101414c04F993947C733: balance==100 - EOA\<newline>115f6e2F70210C14f7DB1AC69737a3CC78435d49: balance==100 - EOA''"
  by eval

lemma "eval0 1000
            SKIP 
            (STR ''089Be5381FcEa58aF334101414c04F993947C733'')
            EMPTY
            EMPTY
            (STR ''0'')
            [(STR ''089Be5381FcEa58aF334101414c04F993947C733'', STR ''100'', EOA, 0), (STR ''115f6e2F70210C14f7DB1AC69737a3CC78435d49'', STR ''100'', EOA, 0)] 
            [(STR ''v1'',(type.Memory (MTArray 5 (MTValue TBool)), Memarr [MBool True, MBool False, MBool True, MBool False, MBool True]))]
       = STR ''v1[0]==true\<newline>v1[1]==false\<newline>v1[2]==true\<newline>v1[3]==false\<newline>v1[4]==true\<newline>089Be5381FcEa58aF334101414c04F993947C733: balance==100 - EOA\<newline>115f6e2F70210C14f7DB1AC69737a3CC78435d49: balance==100 - EOA''"
  by eval

lemma "eval0 1000
            (ITE FALSE (ASSIGN (Id (STR ''x'')) TRUE) (ASSIGN (Id (STR ''y'')) TRUE)) 
            (STR ''089Be5381FcEa58aF334101414c04F993947C733'')
            EMPTY
            EMPTY
            (STR ''0'')
            [(STR ''089Be5381FcEa58aF334101414c04F993947C733'', STR ''100'', EOA, 0), (STR ''115f6e2F70210C14f7DB1AC69737a3CC78435d49'', STR ''100'', EOA, 0)] 
            [(STR ''x'', (Value TBool, Stackbool False)), (STR ''y'', (Value TBool, Stackbool False))]
       = STR ''y==true\<newline>x==false\<newline>089Be5381FcEa58aF334101414c04F993947C733: balance==100 - EOA\<newline>115f6e2F70210C14f7DB1AC69737a3CC78435d49: balance==100 - EOA''"
  by eval

lemma "eval0 1000
            (BLOCK (STR ''v2'', Value TBool, None) (ASSIGN (Id (STR ''v1'')) (LVAL (Id (STR ''v2'')))))
            (STR ''089Be5381FcEa58aF334101414c04F993947C733'')
            EMPTY
            EMPTY
            (STR ''0'')
            [(STR ''089Be5381FcEa58aF334101414c04F993947C733'', STR ''100'', EOA, 0), (STR ''115f6e2F70210C14f7DB1AC69737a3CC78435d49'', STR ''100'', EOA, 0)]
            [(STR ''v1'', (Value TBool, Stackbool True))]
        = STR ''v1==false\<newline>089Be5381FcEa58aF334101414c04F993947C733: balance==100 - EOA\<newline>115f6e2F70210C14f7DB1AC69737a3CC78435d49: balance==100 - EOA''"
  by eval

lemma "eval0 1000
            (ASSIGN (Id (STR ''a_s120_21_m8'')) (LVAL (Id (STR ''a_s120_21_s8''))))
            (STR ''089Be5381FcEa58aF334101414c04F993947C733'')
            EMPTY
            EMPTY
            (STR ''0'')
            [(STR ''089Be5381FcEa58aF334101414c04F993947C733'', STR ''100'', EOA, 0)]
            [((STR ''a_s120_21_s8''), type.Storage (STArray 1 (STArray 2 (STValue (TSInt b120)))), Stoarr [SArray [SInt 347104507864064359095275590289383142, SInt 565831699297331399489670920129618233]]),
             ((STR ''a_s120_21_m8''), type.Memory (MTArray 1 (MTArray 2 (MTValue (TSInt b120)))), Memarr [MArray [MInt (290845675805142398428016622247257774), MInt ((-96834026877269277170645294669272226))]])]
  = STR ''a_s120_21_m8[0][0]==347104507864064359095275590289383142\<newline>a_s120_21_m8[0][1]==565831699297331399489670920129618233\<newline>a_s120_21_s8[0][0]==347104507864064359095275590289383142\<newline>a_s120_21_s8[0][1]==565831699297331399489670920129618233\<newline>089Be5381FcEa58aF334101414c04F993947C733: balance==100 - EOA''"
  by eval

lemma "eval0 1000
            (ASSIGN (Ref (STR ''a_s8_32_m0'') [UINT b8 1]) (LVAL (Ref (STR ''a_s8_31_s7'') [UINT b8 0]))) 
            (STR ''089Be5381FcEa58aF334101414c04F993947C733'')
            EMPTY
            EMPTY
            (STR ''0'')
            [(STR ''089Be5381FcEa58aF334101414c04F993947C733'', STR ''100'', EOA, 0)]
            [(STR ''a_s8_31_s7'', type.Storage (STArray 1 (STArray 3 (STValue (TSInt b8)))), Stoarr [SArray [SInt ((98)), SInt ((-23)), SInt (36)]]),
             (STR ''a_s8_32_m0'', type.Memory (MTArray 2 (MTArray 3 (MTValue (TSInt b8)))), Memarr [MArray [MInt ((-64)), MInt ((39)), MInt ((-125))], MArray [MInt ((-32)), MInt ((-82)), MInt ((-105))]])]
       = STR ''a_s8_32_m0[0][0]==-64\<newline>a_s8_32_m0[0][1]==39\<newline>a_s8_32_m0[0][2]==-125\<newline>a_s8_32_m0[1][0]==98\<newline>a_s8_32_m0[1][1]==-23\<newline>a_s8_32_m0[1][2]==36\<newline>a_s8_31_s7[0][0]==98\<newline>a_s8_31_s7[0][1]==-23\<newline>a_s8_31_s7[0][2]==36\<newline>089Be5381FcEa58aF334101414c04F993947C733: balance==100 - EOA''"
  by eval

lemma "eval0 1000
            SKIP
            (STR ''089Be5381FcEa58aF334101414c04F993947C733'')
            EMPTY
            EMPTY
            (STR ''0'')
            [(STR ''089Be5381FcEa58aF334101414c04F993947C733'', STR ''100'', EOA, 0), (STR ''115f6e2F70210C14f7DB1AC69737a3CC78435d49'', STR ''100'', EOA, 0)]
            [(STR ''v1'', type.Storage (STMap (TUInt b32) (STValue (TUInt b8))), Stomap [(STR ''2129136830'', SInt 247)])]
       = STR ''v1[2129136830]==247\<newline>089Be5381FcEa58aF334101414c04F993947C733: balance==100 - EOA\<newline>115f6e2F70210C14f7DB1AC69737a3CC78435d49: balance==100 - EOA''"
  by eval

definition "testenv1 \<equiv> loadProc (STR ''mycontract'')
              ([(STR ''v1'', Var (STValue TBool)),
                (STR ''m1'', Method ([], True, (ASSIGN (Id (STR ''v1'')) FALSE)))],
                ([], SKIP),
                SKIP)
            fmempty"

global_interpretation soliditytest1: statement_with_gas costs_ex testenv1 costs_min
  defines stmt1 = "soliditytest1.stmt"
      and lexp1 = soliditytest1.lexp 
      and expr1 = soliditytest1.expr
      and ssel1 = soliditytest1.ssel
      and rexp1 = soliditytest1.rexp
      and msel1 = soliditytest1.msel
      and load1 = soliditytest1.load
      and eval1 = soliditytest1.eval
  by unfold_locales auto

lemma "eval1 1000
            (EXTERNAL (ADDRESS (STR ''myaddr'')) (STR ''m1'') [] (UINT b256 0))
            (STR ''local'')
            EMPTY
            (STR ''mycontract'')
            (STR ''0'')
            [(STR ''local'', STR ''100'', EOA, 0), (STR ''myaddr'', STR ''100'', atype.Contract (STR ''mycontract''), 0)]
            []
        = STR ''local: balance==100 - EOA\<newline>myaddr: balance==100 - mycontract(v1==false\<newline>)''"
  by (eval)

lemma "eval1 1000
            (NEW (STR ''mycontract'') [] (UINT b256 10))
            (STR ''local'')
            EMPTY
            (STR ''mycontract'')
            (STR ''0'')
            [(STR ''local'', STR ''100'', EOA, 0), (STR ''myaddr'', STR ''100'', atype.Contract (STR ''mycontract''), 0)]
            []
        = STR ''local: balance==90 - EOA\<newline>0-local: balance==10 - mycontract()\<newline>myaddr: balance==100 - mycontract()''"
  by eval

lemma "eval1 1000
            (
              COMP
                (NEW (STR ''mycontract'') [] (UINT b256 10))
                (EXTERNAL CONTRACTS (STR ''m1'') [] (UINT b256 0))
            )
            (STR ''local'')
            EMPTY
            (STR ''mycontract'')
            (STR ''0'')
            [(STR ''local'', STR ''100'', EOA, 0), (STR ''myaddr'', STR ''100'', atype.Contract (STR ''mycontract''), 0)]
            []
        = STR ''local: balance==90 - EOA\<newline>0-local: balance==10 - mycontract(v1==false\<newline>)\<newline>myaddr: balance==100 - mycontract()''"
  by eval

definition "testenv2 \<equiv> loadProc (STR ''mycontract'')
              ([(STR ''m1'', Function ([], False, UINT b8 5))],
              ([], SKIP),
              SKIP)
            fmempty"

global_interpretation soliditytest2: statement_with_gas costs_ex testenv2 costs_min
  defines stmt2 = "soliditytest2.stmt"
      and lexp2 = soliditytest2.lexp 
      and expr2 = soliditytest2.expr
      and ssel2 = soliditytest2.ssel
      and rexp2 = soliditytest2.rexp
      and msel2 = soliditytest2.msel
      and load2 = soliditytest2.load
      and eval2 = soliditytest2.eval
  by unfold_locales auto

lemma "eval2 1000
            (ASSIGN (Id (STR ''v1'')) (CALL (STR ''m1'') []))
            (STR ''myaddr'')
            (STR ''mycontract'')
            EMPTY
            (STR ''0'')
            [(STR ''myaddr'', STR ''100'', EOA, 0)]
            [(STR ''v1'', (Value (TUInt b8), Stackint 0))]
       = STR ''v1==5\<newline>myaddr: balance==100 - EOA''"
  by (eval)

definition "testenv3 \<equiv> loadProc (STR ''mycontract'')
              ([(STR ''m1'',
                Function ([(STR ''v2'', Value (TSInt b8)), (STR ''v3'', Value (TSInt b8))],
                False,
                PLUS (LVAL (Id (STR ''v2''))) (LVAL (Id (STR ''v3'')))))],
                ([], SKIP),
              SKIP)
            fmempty"

global_interpretation soliditytest3: statement_with_gas costs_ex testenv3 costs_min
  defines stmt3 = "soliditytest3.stmt"
      and lexp3 = soliditytest3.lexp 
      and expr3 = soliditytest3.expr
      and ssel3 = soliditytest3.ssel
      and rexp3 = soliditytest3.rexp
      and msel3 = soliditytest3.msel
      and load3 = soliditytest3.load
      and eval3 = soliditytest3.eval
  by unfold_locales auto

lemma "eval3 1000
            (ASSIGN (Id (STR ''v1'')) (CALL (STR ''m1'') [e.INT b8 3, e.INT b8 4]))
            (STR ''myaddr'')
            (STR ''mycontract'')
            EMPTY
            (STR ''0'')
            [(STR ''myaddr'', STR ''100'', EOA, 0),(STR ''mya'', STR ''100'', EOA, 0)]
            [(STR ''v1'', (Value (TSInt b8), Stackint 0))]
       = STR ''v1==7\<newline>myaddr: balance==100 - EOA\<newline>mya: balance==100 - EOA''"
  by (eval)

definition "testenv4 \<equiv> loadProc (STR ''mycontract'')
              ([(STR ''m1'', Function ([(STR ''v2'', Value (TSInt b8)), (STR ''v3'', Value (TSInt b8))], True, PLUS (LVAL (Id (STR ''v2''))) (LVAL (Id (STR ''v3'')))))],
                ([], SKIP),
                SKIP)
            fmempty"

global_interpretation soliditytest4: statement_with_gas costs_ex testenv4 costs_min
  defines stmt4 = "soliditytest4.stmt"
      and lexp4 = soliditytest4.lexp 
      and expr4 = soliditytest4.expr
      and ssel4 = soliditytest4.ssel
      and rexp4 = soliditytest4.rexp
      and msel4 = soliditytest4.msel
      and load4 = soliditytest4.load
      and eval4 = soliditytest4.eval
  by unfold_locales auto

lemma "eval4 1000
            (ASSIGN (Id (STR ''v1'')) (ECALL (ADDRESS (STR ''extaddr'')) (STR ''m1'') [e.INT b8 3, e.INT b8 4]))
            (STR ''myaddr'')
            EMPTY
            EMPTY
            (STR ''0'')
            [(STR ''myaddr'', STR ''100'', EOA, 0), (STR ''extaddr'', STR ''100'', atype.Contract (STR ''mycontract''), 0)]
            [(STR ''v1'', (Value (TSInt b8), Stackint 0))]
       = STR ''v1==7\<newline>myaddr: balance==100 - EOA\<newline>extaddr: balance==100 - mycontract()''"
  by (eval)

definition "testenv5 \<equiv> loadProc (STR ''mycontract'')
              ([], ([], SKIP), SKIP)
            fmempty"

global_interpretation soliditytest5: statement_with_gas costs_ex testenv5 costs_min
  defines stmt5 = "soliditytest5.stmt"
      and lexp5 = soliditytest5.lexp 
      and expr5 = soliditytest5.expr
      and ssel5 = soliditytest5.ssel
      and rexp5 = soliditytest5.rexp
      and msel5 = soliditytest5.msel
      and load5 = soliditytest5.load
      and eval5 = soliditytest5.eval
  by unfold_locales auto

lemma "eval5 1000
            (TRANSFER (ADDRESS (STR ''myaddr'')) (UINT b256 10))
            (STR ''089Be5381FcEa58aF334101414c04F993947C733'') 
            EMPTY
            EMPTY
            (STR ''0'')
            [(STR ''089Be5381FcEa58aF334101414c04F993947C733'', STR ''100'', EOA, 0), (STR ''myaddr'', STR ''100'', atype.Contract (STR ''mycontract''), 0)] 
            []
       = STR ''089Be5381FcEa58aF334101414c04F993947C733: balance==90 - EOA\<newline>myaddr: balance==110 - mycontract()''"
  by (eval)

definition "testenv6 \<equiv> loadProc (STR ''Receiver'')
              ([(STR ''hello'', Var (STValue TBool))],
              ([], SKIP),
              ASSIGN (Id (STR ''hello'')) TRUE)
            fmempty"

global_interpretation soliditytest6: statement_with_gas costs_ex testenv6 costs_min
  defines stmt6 = "soliditytest6.stmt"
      and lexp6 = soliditytest6.lexp 
      and expr6 = soliditytest6.expr
      and ssel6 = soliditytest6.ssel
      and rexp6 = soliditytest6.rexp
      and msel6 = soliditytest6.msel
      and load6 = soliditytest6.load
      and eval6 = soliditytest6.eval
  by unfold_locales auto

lemma "eval6 1000
          (TRANSFER (ADDRESS (STR ''ReceiverAd'')) (UINT b256 10))
          (STR ''SenderAd'')
          EMPTY
          EMPTY
          (STR ''0'')
          [(STR ''ReceiverAd'', STR ''100'', atype.Contract (STR ''Receiver''), 0), (STR ''SenderAd'', STR ''100'', EOA, 0)]
          []
       = STR ''ReceiverAd: balance==110 - Receiver(hello==true\<newline>)\<newline>SenderAd: balance==90 - EOA''"
  by (eval)

definition "testenv7 \<equiv> loadProc (STR ''mycontract'')
             ([], ([], SKIP), SKIP)
             fmempty"

global_interpretation soliditytest7: statement_with_gas costs_ex testenv7 costs_min
  defines stmt7 = "soliditytest7.stmt"
      and lexp7 = soliditytest7.lexp 
      and expr7 = soliditytest7.expr
      and ssel7 = soliditytest7.ssel
      and rexp7 = soliditytest7.rexp
      and msel7 = soliditytest7.msel
      and load7 = soliditytest7.load
      and eval7 = soliditytest7.eval
  by unfold_locales auto

lemma "eval7 1000
            (COMP(COMP(((ASSIGN (Id (STR ''x''))  (e.UINT b8 0))))(TRANSFER (ADDRESS (STR ''myaddr'')) (UINT b256 5)))(SKIP))
            (STR ''089Be5381FcEa58aF334101414c04F993947C733'')
            EMPTY
            EMPTY
            (STR ''0'')
            [(STR ''089Be5381FcEa58aF334101414c04F993947C733'', STR ''100'', EOA, 0), (STR ''myaddr'', STR ''100'', atype.Contract (STR ''mycontract''),0)]
            [(STR ''x'', (Value (TUInt b8), Stackint 9))]
       = STR ''x==0\<newline>089Be5381FcEa58aF334101414c04F993947C733: balance==95 - EOA\<newline>myaddr: balance==105 - mycontract()''"
  by (eval)

subsection\<open>The Final Code Export\<close>

consts ReadL\<^sub>S   :: "String.literal \<Rightarrow> s"
consts ReadL\<^sub>a\<^sub>c\<^sub>c :: "String.literal \<Rightarrow> (String.literal \<times> String.literal \<times> atype \<times> nat) list"
consts ReadL\<^sub>d\<^sub>a\<^sub>t :: "String.literal \<Rightarrow> (String.literal \<times> type \<times> data\<^sub>E\<^sub>n\<^sub>v\<^sub>i\<^sub>r\<^sub>o\<^sub>n\<^sub>m\<^sub>e\<^sub>n\<^sub>t) list"
consts ReadL\<^sub>P :: "String.literal \<Rightarrow> data\<^sub>P list"

code_printing 
   constant ReadL\<^sub>S  \<rightharpoonup> (Haskell) "Prelude.read"
 | constant ReadL\<^sub>a\<^sub>c\<^sub>c \<rightharpoonup> (Haskell) "Prelude.read"
 | constant ReadL\<^sub>d\<^sub>a\<^sub>t \<rightharpoonup> (Haskell) "Prelude.read"
 | constant ReadL\<^sub>P \<rightharpoonup> (Haskell) "Prelude.read"

fun main_stub :: "String.literal list \<Rightarrow> (int \<times> String.literal)"
  where
   "main_stub [stm, saddr, name, raddr, val, acc, dat]
        = (0, eval0 1000 (ReadL\<^sub>S stm) saddr name raddr val (ReadL\<^sub>a\<^sub>c\<^sub>c acc) (ReadL\<^sub>d\<^sub>a\<^sub>t dat))"
 | "main_stub _ = (2, 
          STR ''solidity-evaluator [credit] \"Statement\" \"ContractAddress\" \"OriginAddress\" \"Value\"\<newline>''
        + STR ''  \"(Address * balance) list\" \"(Address * ((identifier * member) list) * Statement)\" \"(Variable * type * Value) list\"\<newline>''
        + STR ''\<newline>'')"

generate_file "code/solidity-evaluator/app/Main.hs" = \<open>
module Main where
import System.Environment
import Solidity_Evaluator
import Prelude

main :: IO ()
main = do
  args <- getArgs
  Prelude.putStr(snd $ Solidity_Evaluator.main_stub args) 
\<close>

export_generated_files _

export_code eval0 SKIP main_stub
            in Haskell module_name "Solidity_Evaluator" file_prefix "solidity-evaluator/src"  (string_classes)   

subsection\<open>Demonstrating the Symbolic Execution of Solidity\<close>

subsubsection\<open>Simple Examples  \<close> 
lemma "msel True (MTArray 5 (MTArray 6 (MTValue TBool))) (STR ''2'') [UINT b8 3] eempty emptyTypedStore (mystate\<lparr>state.Gas:=1\<rparr>) 1
= Normal ((STR ''3.2'', MTArray 6 (MTValue TBool)), 1)"  by Solidity_Symbex.solidity_symbex

lemma "msel True (MTArray 5 (MTArray 6 (MTValue TBool))) (STR ''2'') [UINT b8 3, UINT b8 4] eempty emptyTypedStore (mystate\<lparr>state.Gas:=1,Memory:=mymemory2\<rparr>) 1
= Normal ((STR ''4.5'', MTValue TBool), 1)" by Solidity_Symbex.solidity_symbex

lemma "msel True (MTArray 5 (MTArray 6 (MTValue TBool))) (STR ''2'') [UINT b8 5] eempty emptyTypedStore (mystate\<lparr>state.Gas:=1,Memory:=mymemory2\<rparr>) 1
= Exception (Err)" by Solidity_Symbex.solidity_symbex

subsubsection\<open>A More Complex Example Including Memory Copy\<close> 

abbreviation P1::s
  where "P1 \<equiv> COMP (ASSIGN (Id (STR ''sa'')) (LVAL (Id (STR ''ma''))))
                   (ASSIGN (Ref (STR ''sa'') [UINT b8 0]) TRUE)"
abbreviation myenv::environment
  where "myenv \<equiv> updateEnv (STR ''ma'') (type.Memory (MTArray 1 (MTValue TBool))) (Stackloc (STR ''1''))
                 (updateEnv (STR ''sa'') (type.Storage (STArray 1 (STValue TBool))) (Storeloc (STR ''1''))
                 (emptyEnv (STR ''ad'') EMPTY (STR ''ad'') (STR ''0'')))"
 
abbreviation mystack::stack
  where "mystack \<equiv> updateStore (STR ''1'') (KMemptr (STR ''1'')) emptyStore"
 
abbreviation mystore::"address \<Rightarrow> storageT"
  where "mystore \<equiv> \<lambda> _ . fmempty"
 
abbreviation mymemory::memoryT
  where "mymemory \<equiv> updateTypeStore (STR ''0.1'') (MTValue TBool) (updateStore (STR ''0.1'') (MValue (STR ''False'')) emptyTypedStore)"

abbreviation mystorage::storageT
  where "mystorage \<equiv> fmupd (STR ''0.1'') (STR ''True'') fmempty"

declare[[ML_print_depth = 10000]]
value \<open>(stmt P1 myenv emptyTypedStore \<lparr>Accounts=emptyAccount, Stack=mystack, Memory=mymemory, Storage=(mystore ((STR ''ad''):= mystorage)), state.Gas=1000\<rparr>)\<close>  


lemma \<open>(stmt P1 myenv emptyTypedStore \<lparr>Accounts=emptyAccount, Stack=mystack, Memory=mymemory, Storage=(mystore ((STR ''ad''):= mystorage)), state.Gas=1000\<rparr>)
      = Normal ((), \<lparr>Accounts = emptyAccount, Stack = \<lparr>Mapping = fmap_of_list [(STR ''1'', KMemptr STR ''1'')], Toploc = 0\<rparr>,
                   Memory = \<lparr>Mapping = fmap_of_list [(STR ''0.1'', MValue STR ''False'')], Toploc = 0, Typed_Mapping= fmap_of_list [(STR ''0.1'', MTValue TBool)]\<rparr>, Storage = (mystore ((STR ''ad''):= mystorage)), state.Gas = 1000\<rparr>) \<close>  
    by(solidity_symbex)

end
