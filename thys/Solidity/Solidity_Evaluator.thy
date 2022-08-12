section\<open> Solidty Evaluator and Code Generator Setup\<close>

theory
  Solidity_Evaluator
imports
  Solidity_Main
  "HOL-Library.Code_Target_Numeral"
  "HOL-Library.Sublist"
  "HOL-Library.Finite_Map"
begin

subsection\<open>Code Generator Setup and Local Tests\<close>


subsubsection\<open>Utils\<close>

definition FAILURE::"String.literal" where "FAILURE = STR ''Failure''"
definition "inta_of_int = int o nat_of_integer"
definition "nat_of_int  = nat_of_integer"

fun astore :: "Identifier \<Rightarrow> Type \<Rightarrow> Valuetype \<Rightarrow> StorageT * Environment \<Rightarrow> StorageT * Environment"
  where "astore i t v (s, e) = (fmupd i v s, (updateEnv i t (Storeloc i) e))"

subsubsection\<open>Valuetypes\<close>

fun dump\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e\<^sub>t\<^sub>y\<^sub>p\<^sub>e\<^sub>s::"Types \<Rightarrow> Valuetype \<Rightarrow> String.literal" where
   "dump\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e\<^sub>t\<^sub>y\<^sub>p\<^sub>e\<^sub>s (TSInt _) n = n"
 | "dump\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e\<^sub>t\<^sub>y\<^sub>p\<^sub>e\<^sub>s (TUInt _) n = n"
 | "dump\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e\<^sub>t\<^sub>y\<^sub>p\<^sub>e\<^sub>s TBool b = (if b = (STR ''True'') then  STR ''true'' else STR ''false'')"
 | "dump\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e\<^sub>t\<^sub>y\<^sub>p\<^sub>e\<^sub>s TAddr ad = ad"

paragraph\<open>Generalized Unit Tests\<close>

lemma  "createSInt 8 500 = STR ''-12''"
  by(eval)

lemma "STR ''-92134039538802366542421159375273829975'' 
      = createSInt 128 45648483135649456465465452123894894554654654654654646999465"
  by(eval)

lemma "STR ''-128'' = createSInt 8 (-128)"
  by(eval)

lemma "STR ''244'' = (createUInt 8 500)"
  by(eval)

lemma "STR ''220443428915524155977936330922349307608'' 
      = (createUInt 128 4564848313564945646546545212389489455465465465465464699946544654654654654168)"
  by(eval)

lemma "less (TUInt 144) (TSInt 160) (STR ''5'') (STR ''8'') = Some(STR ''True'', TBool) "
  by(eval)


subsubsection\<open>Load: Accounts\<close>

fun load\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t\<^sub>s :: "Accounts \<Rightarrow> (Address \<times> Balance) list \<Rightarrow> Accounts" where 
   "load\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t\<^sub>s acc []             = acc"
 | "load\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t\<^sub>s acc ((ad, bal)#as) = load\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t\<^sub>s (updateBalance ad bal acc) as"

definition dump\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t\<^sub>s :: "Accounts \<Rightarrow> Address list \<Rightarrow> String.literal"
where
  "dump\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t\<^sub>s acc = foldl (\<lambda> t a . String.implode (    (String.explode t) 
                                                     @ (String.explode a) 
                                                     @ ''.balance'' 
                                                     @ ''=='' 
                                                     @ String.explode (accessBalance acc a) 
                                                     @ ''\<newline>'')) 
                          (STR '''')"

definition init\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t::"(Address \<times> Balance) list => Accounts" where 
  "init\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t = load\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t\<^sub>s emptyAccount"


subsubsection\<open>Load: Store\<close>

type_synonym Data\<^sub>S\<^sub>t\<^sub>o\<^sub>r\<^sub>e = "(Location \<times> String.literal) list"

fun show\<^sub>S\<^sub>t\<^sub>o\<^sub>r\<^sub>e::"'a Store \<Rightarrow> 'a fset" where
    "show\<^sub>S\<^sub>t\<^sub>o\<^sub>r\<^sub>e s = (fmran (mapping s))"

subsubsection\<open>Load: Memory\<close>

datatype Data\<^sub>M\<^sub>e\<^sub>m\<^sub>o\<^sub>r\<^sub>y = MArray "Data\<^sub>M\<^sub>e\<^sub>m\<^sub>o\<^sub>r\<^sub>y list"
  | MBool bool
  | MInt int
  | MAddress Address

fun 
 loadRec\<^sub>M\<^sub>e\<^sub>m\<^sub>o\<^sub>r\<^sub>y :: "Location \<Rightarrow> Data\<^sub>M\<^sub>e\<^sub>m\<^sub>o\<^sub>r\<^sub>y \<Rightarrow> MemoryT \<Rightarrow> MemoryT" where
"loadRec\<^sub>M\<^sub>e\<^sub>m\<^sub>o\<^sub>r\<^sub>y loc (MArray dat) mem = 
(fst (foldl (\<lambda> S d . let (s',x) = S in  (loadRec\<^sub>M\<^sub>e\<^sub>m\<^sub>o\<^sub>r\<^sub>y (hash loc (ShowL\<^sub>n\<^sub>a\<^sub>t x)) d s', Suc x)) (updateStore loc (MPointer loc) mem,0) dat))"
| "loadRec\<^sub>M\<^sub>e\<^sub>m\<^sub>o\<^sub>r\<^sub>y loc (MBool b) mem = updateStore loc ((MValue \<circ> ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l) b) mem "
| "loadRec\<^sub>M\<^sub>e\<^sub>m\<^sub>o\<^sub>r\<^sub>y loc (MInt i) mem = updateStore loc ((MValue \<circ> ShowL\<^sub>i\<^sub>n\<^sub>t) i) mem "
| "loadRec\<^sub>M\<^sub>e\<^sub>m\<^sub>o\<^sub>r\<^sub>y loc (MAddress ad) mem = updateStore loc (MValue ad) mem"

definition load\<^sub>M\<^sub>e\<^sub>m\<^sub>o\<^sub>r\<^sub>y :: "Data\<^sub>M\<^sub>e\<^sub>m\<^sub>o\<^sub>r\<^sub>y list \<Rightarrow> MemoryT \<Rightarrow> MemoryT" where
"load\<^sub>M\<^sub>e\<^sub>m\<^sub>o\<^sub>r\<^sub>y dat mem = (let l     = ShowL\<^sub>n\<^sub>a\<^sub>t (toploc mem);
                         (m, _) = foldl (\<lambda> (m',x) d . (loadRec\<^sub>M\<^sub>e\<^sub>m\<^sub>o\<^sub>r\<^sub>y (((hash l) \<circ> ShowL\<^sub>n\<^sub>a\<^sub>t) x) d m', Suc x)) (mem, 0) dat
    in (snd \<circ> allocate) m)"

                          
fun  dumprec\<^sub>M\<^sub>e\<^sub>m\<^sub>o\<^sub>r\<^sub>y:: "Location \<Rightarrow> MTypes \<Rightarrow> MemoryT \<Rightarrow> String.literal \<Rightarrow> String.literal \<Rightarrow> String.literal" where
"dumprec\<^sub>M\<^sub>e\<^sub>m\<^sub>o\<^sub>r\<^sub>y loc tp mem ls str = ( case accessStore loc mem of
    Some (MPointer l) \<Rightarrow> ( case tp of
        (MTArray x t) \<Rightarrow> iter (\<lambda> i str' . dumprec\<^sub>M\<^sub>e\<^sub>m\<^sub>o\<^sub>r\<^sub>y ((hash l o ShowL\<^sub>i\<^sub>n\<^sub>t) i) t mem 
                           (ls + (STR ''['') + (ShowL\<^sub>i\<^sub>n\<^sub>t i) + (STR '']'')) str') str x
       | _ \<Rightarrow> FAILURE)
    | Some (MValue v) \<Rightarrow> (case tp of
        MTValue t \<Rightarrow> str + ls + (STR ''=='') + dump\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e\<^sub>t\<^sub>y\<^sub>p\<^sub>e\<^sub>s t v + (STR ''\<newline>'')
       | _ \<Rightarrow> FAILURE)
   | None \<Rightarrow> FAILURE)"

definition dump\<^sub>M\<^sub>e\<^sub>m\<^sub>o\<^sub>r\<^sub>y :: "Location \<Rightarrow> int \<Rightarrow> MTypes \<Rightarrow> MemoryT \<Rightarrow> String.literal \<Rightarrow>String.literal \<Rightarrow>String.literal" where
"dump\<^sub>M\<^sub>e\<^sub>m\<^sub>o\<^sub>r\<^sub>y loc x t mem ls str = iter (\<lambda>i. dumprec\<^sub>M\<^sub>e\<^sub>m\<^sub>o\<^sub>r\<^sub>y ((hash loc (ShowL\<^sub>i\<^sub>n\<^sub>t i))) t mem (ls + STR ''['' + (ShowL\<^sub>i\<^sub>n\<^sub>t i + STR '']''))) str x"

subsubsection\<open>Storage\<close>

datatype Data\<^sub>S\<^sub>t\<^sub>o\<^sub>r\<^sub>a\<^sub>g\<^sub>e =
    SArray "Data\<^sub>S\<^sub>t\<^sub>o\<^sub>r\<^sub>a\<^sub>g\<^sub>e list" |
    SMap "(String.literal \<times> Data\<^sub>S\<^sub>t\<^sub>o\<^sub>r\<^sub>a\<^sub>g\<^sub>e) list" |
    SBool bool |
    SInt int |
    SAddress Address

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

definition tolist :: "Location \<Rightarrow> String.literal list" where 
"tolist s = map String.implode (splitOn (CHR ''.'') (String.explode s))"

abbreviation convert :: "Location \<Rightarrow> Location"
  where "convert loc \<equiv> (if loc= STR ''True'' then STR ''true'' else
    if loc=STR ''False'' then STR ''false'' else loc)"

fun go\<^sub>S\<^sub>t\<^sub>o\<^sub>r\<^sub>a\<^sub>g\<^sub>e :: "Location \<Rightarrow> (String.literal \<times>  STypes) \<Rightarrow> (String.literal \<times> STypes)" where
  "go\<^sub>S\<^sub>t\<^sub>o\<^sub>r\<^sub>a\<^sub>g\<^sub>e l (s, STArray _ t) = (s + (STR ''['') + (convert l) + (STR '']''), t)"
| "go\<^sub>S\<^sub>t\<^sub>o\<^sub>r\<^sub>a\<^sub>g\<^sub>e l (s, STMap _ t) = (s + (STR ''['') + (convert l) + (STR '']''), t)"
| "go\<^sub>S\<^sub>t\<^sub>o\<^sub>r\<^sub>a\<^sub>g\<^sub>e l (s, STValue t) = (s + (STR ''['') + (convert l) + (STR '']''), STValue t)"

fun dumpSingle\<^sub>S\<^sub>t\<^sub>o\<^sub>r\<^sub>a\<^sub>g\<^sub>e :: "StorageT \<Rightarrow> String.literal \<Rightarrow> STypes \<Rightarrow> (Location \<times> Location) \<Rightarrow> String.literal \<Rightarrow> String.literal" where
"dumpSingle\<^sub>S\<^sub>t\<^sub>o\<^sub>r\<^sub>a\<^sub>g\<^sub>e sto id' tp (loc,l) str =
    (case foldr go\<^sub>S\<^sub>t\<^sub>o\<^sub>r\<^sub>a\<^sub>g\<^sub>e (tolist loc) (str + id', tp)  of
        (s, STValue t) \<Rightarrow> (case fmlookup sto (loc + l) of
            Some v \<Rightarrow> s + (STR ''=='') + dump\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e\<^sub>t\<^sub>y\<^sub>p\<^sub>e\<^sub>s t v
           | None \<Rightarrow> FAILURE)
        | _ \<Rightarrow> FAILURE)"

                            
definition \<open>sorted_list_of_set' \<equiv> map_fun id id (folding_on.F insort [])\<close>

lemma sorted_list_of_fset'_def': \<open>sorted_list_of_set' = sorted_list_of_set\<close>
  apply(rule ext)
  by (simp add: sorted_list_of_set'_def sorted_list_of_set_def sorted_key_list_of_set_def)

lemma sorted_list_of_set_sort_remdups' [code]:
  \<open>sorted_list_of_set' (set xs) = sort (remdups xs)\<close>
  using sorted_list_of_fset'_def' sorted_list_of_set_sort_remdups                      
  by metis

definition  locations_map :: "Location \<Rightarrow> (Location, 'v) fmap \<Rightarrow> Location list" where
"locations_map loc = (filter (isSuffixOf ((STR ''.'')+loc))) \<circ>  sorted_list_of_set' \<circ> fset \<circ> fmdom"

definition  locations :: "Location \<Rightarrow> 'v Store \<Rightarrow> Location list" where
"locations loc = locations_map loc \<circ> mapping"

fun dump\<^sub>S\<^sub>t\<^sub>o\<^sub>r\<^sub>a\<^sub>g\<^sub>e ::  "StorageT \<Rightarrow> Location \<Rightarrow> String.literal \<Rightarrow> STypes \<Rightarrow> String.literal \<Rightarrow> String.literal"
where
"dump\<^sub>S\<^sub>t\<^sub>o\<^sub>r\<^sub>a\<^sub>g\<^sub>e sto loc id' (STArray _ t) str = foldl 
      (\<lambda> s l . dumpSingle\<^sub>S\<^sub>t\<^sub>o\<^sub>r\<^sub>a\<^sub>g\<^sub>e sto id' t ((splitAt (length (String.explode l) - length (String.explode loc) - 1) l)) s 
           + (STR ''\<newline>'')) str (locations_map loc sto)"
| "dump\<^sub>S\<^sub>t\<^sub>o\<^sub>r\<^sub>a\<^sub>g\<^sub>e sto loc id' (STMap _ t) str = 
   foldl (\<lambda> s l . dumpSingle\<^sub>S\<^sub>t\<^sub>o\<^sub>r\<^sub>a\<^sub>g\<^sub>e sto id' t (splitAt (length (String.explode l) - length (String.explode loc) - 1) l) s + (STR ''\<newline>'')) str 
(locations_map loc sto)"
  | "dump\<^sub>S\<^sub>t\<^sub>o\<^sub>r\<^sub>a\<^sub>g\<^sub>e sto loc id' (STValue t) str = (case fmlookup sto loc of
      Some v \<Rightarrow> str + id' + (STR ''=='') + dump\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e\<^sub>t\<^sub>y\<^sub>p\<^sub>e\<^sub>s t v + (STR ''\<newline>'')
    | _ \<Rightarrow> str)"


fun loadRec\<^sub>S\<^sub>t\<^sub>o\<^sub>r\<^sub>a\<^sub>g\<^sub>e :: "Location \<Rightarrow> Data\<^sub>S\<^sub>t\<^sub>o\<^sub>r\<^sub>a\<^sub>g\<^sub>e \<Rightarrow> StorageT \<Rightarrow> StorageT" where
"loadRec\<^sub>S\<^sub>t\<^sub>o\<^sub>r\<^sub>a\<^sub>g\<^sub>e loc (SArray dat) sto = fst (foldl (\<lambda> S d . let (s', x) = S in (loadRec\<^sub>S\<^sub>t\<^sub>o\<^sub>r\<^sub>a\<^sub>g\<^sub>e (hash loc (ShowL\<^sub>n\<^sub>a\<^sub>t x)) d s', Suc x)) (sto,0) dat)"
| "loadRec\<^sub>S\<^sub>t\<^sub>o\<^sub>r\<^sub>a\<^sub>g\<^sub>e loc (SMap dat) sto  = ( foldr (\<lambda> (k, v) s'. loadRec\<^sub>S\<^sub>t\<^sub>o\<^sub>r\<^sub>a\<^sub>g\<^sub>e (hash loc k) v s') dat sto)"
| "loadRec\<^sub>S\<^sub>t\<^sub>o\<^sub>r\<^sub>a\<^sub>g\<^sub>e loc (SBool b) sto = fmupd loc (ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l b) sto"
| "loadRec\<^sub>S\<^sub>t\<^sub>o\<^sub>r\<^sub>a\<^sub>g\<^sub>e loc (SInt i)  sto = fmupd loc (ShowL\<^sub>i\<^sub>n\<^sub>t i) sto"
| "loadRec\<^sub>S\<^sub>t\<^sub>o\<^sub>r\<^sub>a\<^sub>g\<^sub>e loc (SAddress ad) sto = fmupd loc ad sto"

subsubsection\<open>Environment\<close>

datatype Data\<^sub>E\<^sub>n\<^sub>v\<^sub>i\<^sub>r\<^sub>o\<^sub>n\<^sub>m\<^sub>e\<^sub>n\<^sub>t =
    Memarr "Data\<^sub>M\<^sub>e\<^sub>m\<^sub>o\<^sub>r\<^sub>y list" |
    CDarr "Data\<^sub>M\<^sub>e\<^sub>m\<^sub>o\<^sub>r\<^sub>y list" |
    Stoarr "Data\<^sub>S\<^sub>t\<^sub>o\<^sub>r\<^sub>a\<^sub>g\<^sub>e list"|
    Stomap "(String.literal \<times> Data\<^sub>S\<^sub>t\<^sub>o\<^sub>r\<^sub>a\<^sub>g\<^sub>e) list" |
    Stackbool bool |
    Stobool bool |
    Stackint int |
    Stoint int |
    Stackaddr Address |
    Stoaddr Address

fun loadsimple\<^sub>E\<^sub>n\<^sub>v\<^sub>i\<^sub>r\<^sub>o\<^sub>n\<^sub>m\<^sub>e\<^sub>n\<^sub>t :: "(Stack \<times> CalldataT \<times> MemoryT \<times> StorageT \<times> Environment) 
                    \<Rightarrow> (Identifier \<times> Type \<times> Data\<^sub>E\<^sub>n\<^sub>v\<^sub>i\<^sub>r\<^sub>o\<^sub>n\<^sub>m\<^sub>e\<^sub>n\<^sub>t) \<Rightarrow> (Stack \<times> CalldataT \<times> MemoryT \<times> StorageT \<times> Environment)"
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
        let l = ShowL\<^sub>n\<^sub>a\<^sub>t (toploc c);
            c' = load\<^sub>M\<^sub>e\<^sub>m\<^sub>o\<^sub>r\<^sub>y a c;
            (k', e') = astack id' tp (KCDptr l) (k, e)
        in (k', c', m, s, e')
  |  Memarr a \<Rightarrow>
        let l = ShowL\<^sub>n\<^sub>a\<^sub>t (toploc m);
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

definition load\<^sub>E\<^sub>n\<^sub>v\<^sub>i\<^sub>r\<^sub>o\<^sub>n\<^sub>m\<^sub>e\<^sub>n\<^sub>t::"(Stack \<times> CalldataT \<times> MemoryT \<times> StorageT \<times> Environment) \<Rightarrow> (Identifier \<times> Type \<times> Data\<^sub>E\<^sub>n\<^sub>v\<^sub>i\<^sub>r\<^sub>o\<^sub>n\<^sub>m\<^sub>e\<^sub>n\<^sub>t) list
                       \<Rightarrow> (Stack \<times> CalldataT \<times> MemoryT \<times> StorageT \<times> Environment)"
  where
"load\<^sub>E\<^sub>n\<^sub>v\<^sub>i\<^sub>r\<^sub>o\<^sub>n\<^sub>m\<^sub>e\<^sub>n\<^sub>t = foldl loadsimple\<^sub>E\<^sub>n\<^sub>v\<^sub>i\<^sub>r\<^sub>o\<^sub>n\<^sub>m\<^sub>e\<^sub>n\<^sub>t"

definition getValue\<^sub>E\<^sub>n\<^sub>v\<^sub>i\<^sub>r\<^sub>o\<^sub>n\<^sub>m\<^sub>e\<^sub>n\<^sub>t :: "Stack \<Rightarrow> CalldataT \<Rightarrow> MemoryT \<Rightarrow> StorageT \<Rightarrow> Environment \<Rightarrow> Identifier \<Rightarrow> String.literal \<Rightarrow> String.literal"
  where 
"getValue\<^sub>E\<^sub>n\<^sub>v\<^sub>i\<^sub>r\<^sub>o\<^sub>n\<^sub>m\<^sub>e\<^sub>n\<^sub>t k c m s e i txt = (case fmlookup (denvalue e) i of
    Some (tp, Stackloc l) \<Rightarrow> (case accessStore l k of
        Some (KValue v) \<Rightarrow> (case tp of
            Value t \<Rightarrow> (txt + i + (STR ''=='') + dump\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e\<^sub>t\<^sub>y\<^sub>p\<^sub>e\<^sub>s t v + (STR ''\<newline>''))
          |  _ \<Rightarrow> FAILURE)
      | Some (KCDptr p) \<Rightarrow> (case tp of
            Calldata (MTArray x t) \<Rightarrow> dump\<^sub>M\<^sub>e\<^sub>m\<^sub>o\<^sub>r\<^sub>y p x t c i txt
            | _ \<Rightarrow> FAILURE)
      | Some (KMemptr p) \<Rightarrow> (case tp of
            Memory (MTArray x t) \<Rightarrow> dump\<^sub>M\<^sub>e\<^sub>m\<^sub>o\<^sub>r\<^sub>y p x t m i txt
            | _ \<Rightarrow> FAILURE)
      | Some (KStoptr p) \<Rightarrow> (case tp of
            Storage t \<Rightarrow> dump\<^sub>S\<^sub>t\<^sub>o\<^sub>r\<^sub>a\<^sub>g\<^sub>e s p i t txt
            | _ \<Rightarrow> FAILURE))
   | Some (Storage t, Storeloc l) \<Rightarrow> dump\<^sub>S\<^sub>t\<^sub>o\<^sub>r\<^sub>a\<^sub>g\<^sub>e s l i t txt
   | _ \<Rightarrow> FAILURE
)"

type_synonym Data\<^sub>P = "(Address \<times> ((Identifier \<times> Member) list \<times> S))"

definition dump\<^sub>E\<^sub>n\<^sub>v\<^sub>i\<^sub>r\<^sub>o\<^sub>n\<^sub>m\<^sub>e\<^sub>n\<^sub>t :: "Stack  \<Rightarrow> CalldataT \<Rightarrow> MemoryT \<Rightarrow> StorageT \<Rightarrow> Environment \<Rightarrow> Identifier list \<Rightarrow> String.literal" 
  where "dump\<^sub>E\<^sub>n\<^sub>v\<^sub>i\<^sub>r\<^sub>o\<^sub>n\<^sub>m\<^sub>e\<^sub>n\<^sub>t k c m s e sl = foldr (getValue\<^sub>E\<^sub>n\<^sub>v\<^sub>i\<^sub>r\<^sub>o\<^sub>n\<^sub>m\<^sub>e\<^sub>n\<^sub>t k c m s e) sl  (STR '''')"

fun loadProc::"Environment\<^sub>P \<Rightarrow> Data\<^sub>P \<Rightarrow> Environment\<^sub>P"
  where "loadProc e\<^sub>P (ad, (xs, fb)) = fmupd ad (fmap_of_list xs, fb) e\<^sub>P"

fun initStorage::"(Address \<times> Balance) list \<Rightarrow> (Address, StorageT) fmap \<Rightarrow> (Address, StorageT) fmap"
  where "initStorage [] m = m"
  | "initStorage (x # xs) m = fmupd (fst x) (fmempty) m"

subsection\<open>Test Setup\<close>

definition eval::"Gas \<Rightarrow> (S \<Rightarrow> Environment\<^sub>P \<Rightarrow> Environment \<Rightarrow> CalldataT \<Rightarrow> (unit, Ex, State) state_monad)
                 \<Rightarrow> S \<Rightarrow> Address \<Rightarrow> Address \<Rightarrow> Valuetype \<Rightarrow> (Address \<times> Balance) list 
                 \<Rightarrow> Data\<^sub>P list
                 \<Rightarrow> (String.literal \<times> Type \<times> Data\<^sub>E\<^sub>n\<^sub>v\<^sub>i\<^sub>r\<^sub>o\<^sub>n\<^sub>m\<^sub>e\<^sub>n\<^sub>t) list
          \<Rightarrow> String.literal"
  where "eval g stmt\<^sub>e\<^sub>v\<^sub>a\<^sub>l stm addr adest aval acc d dat
        = (let (k,c,m,s,e) = load\<^sub>E\<^sub>n\<^sub>v\<^sub>i\<^sub>r\<^sub>o\<^sub>n\<^sub>m\<^sub>e\<^sub>n\<^sub>t (emptyStore, emptyStore, emptyStore, fmempty, emptyEnv addr adest aval) dat;
               e\<^sub>p        = foldl loadProc fmempty d;
               a         = init\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t acc;
               s'        = fmupd addr s (initStorage acc fmempty);
               z         = \<lparr>accounts=a,stack=k,memory=m,storage=s',gas=g\<rparr> 
           in (
             case (stmt\<^sub>e\<^sub>v\<^sub>a\<^sub>l stm e\<^sub>p e c z) of
              Normal ((), z') \<Rightarrow> (dump\<^sub>E\<^sub>n\<^sub>v\<^sub>i\<^sub>r\<^sub>o\<^sub>n\<^sub>m\<^sub>e\<^sub>n\<^sub>t (stack z') c (memory z') (the (fmlookup (storage z') addr)) e (map (\<lambda> (a,b,c). a) dat))
                             + (dump\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t\<^sub>s (accounts z') (map fst acc))
             | Exception Err   \<Rightarrow> STR ''Exception''
             | Exception Gas   \<Rightarrow> STR ''OutOfGas''))"

value "eval 1
            stmt
            SKIP 
            (STR ''089Be5381FcEa58aF334101414c04F993947C733'')
            (STR '''')
            (STR ''0'')
            [(STR ''089Be5381FcEa58aF334101414c04F993947C733'', STR ''100''),(STR ''115f6e2F70210C14f7DB1AC69737a3CC78435d49'', STR ''100'')] 
            []
            [(STR ''v1'', (Value TBool, Stackbool True))]"

lemma "eval 1000
            stmt
            SKIP 
            (STR ''089Be5381FcEa58aF334101414c04F993947C733'') 
            (STR '''')
            (STR ''0'')
            [(STR ''089Be5381FcEa58aF334101414c04F993947C733'', STR ''100''), (STR ''115f6e2F70210C14f7DB1AC69737a3CC78435d49'', STR ''100'')] 
            []
            [(STR ''v1'', (Value TBool, Stackbool True))]
     = STR ''v1==true\<newline>089Be5381FcEa58aF334101414c04F993947C733.balance==100\<newline>115f6e2F70210C14f7DB1AC69737a3CC78435d49.balance==100\<newline>''"
  by(eval)

value "eval 1000
            stmt
            SKIP
            (STR ''089Be5381FcEa58aF334101414c04F993947C733'')
            (STR '''')
            (STR ''0'')
            [(STR ''089Be5381FcEa58aF334101414c04F993947C733'', STR ''100''), (STR ''115f6e2F70210C14f7DB1AC69737a3CC78435d49'', STR ''100'')] 
            []
            [(STR ''v1'', (Storage (STArray 5 (STValue TBool)), Stoarr [SBool True, SBool False, SBool True, SBool False, SBool True]))]"


lemma "eval 1000
            stmt
            SKIP 
            (STR ''089Be5381FcEa58aF334101414c04F993947C733'')
            (STR '''')
            (STR ''0'')
            [(STR ''089Be5381FcEa58aF334101414c04F993947C733'', STR ''100''), (STR ''115f6e2F70210C14f7DB1AC69737a3CC78435d49'', STR ''100'')] 
            []
            [(STR ''v1'',(Memory (MTArray 5 (MTValue TBool)), Memarr [MBool True, MBool False, MBool True, MBool False, MBool True]))]
       = STR ''v1[0]==true\<newline>v1[1]==false\<newline>v1[2]==true\<newline>v1[3]==false\<newline>v1[4]==true\<newline>089Be5381FcEa58aF334101414c04F993947C733.balance==100\<newline>115f6e2F70210C14f7DB1AC69737a3CC78435d49.balance==100\<newline>''"
  by(eval)

lemma "eval 1000
            stmt
            (ITE FALSE (ASSIGN (Id (STR ''x'')) TRUE) (ASSIGN (Id (STR ''y'')) TRUE)) 
            (STR ''089Be5381FcEa58aF334101414c04F993947C733'')
            (STR '''')
            (STR ''0'')
            [(STR ''089Be5381FcEa58aF334101414c04F993947C733'', STR ''100''), (STR ''115f6e2F70210C14f7DB1AC69737a3CC78435d49'', STR ''100'')] 
            []
            [(STR ''x'', (Value TBool, Stackbool False)), (STR ''y'', (Value TBool, Stackbool False))]
       = STR ''y==true\<newline>x==false\<newline>089Be5381FcEa58aF334101414c04F993947C733.balance==100\<newline>115f6e2F70210C14f7DB1AC69737a3CC78435d49.balance==100\<newline>''"
  by(eval)

lemma "eval 1000
            stmt
            (BLOCK ((STR ''v2'', Value TBool), None) (ASSIGN (Id (STR ''v1'')) (LVAL (Id (STR ''v2'')))))
            (STR ''089Be5381FcEa58aF334101414c04F993947C733'')
            (STR '''')
            (STR ''0'')
            [(STR ''089Be5381FcEa58aF334101414c04F993947C733'', STR ''100''), (STR ''115f6e2F70210C14f7DB1AC69737a3CC78435d49'', STR ''100'')]
            []
            [(STR ''v1'', (Value TBool, Stackbool True))]
        = STR ''v1==false\<newline>089Be5381FcEa58aF334101414c04F993947C733.balance==100\<newline>115f6e2F70210C14f7DB1AC69737a3CC78435d49.balance==100\<newline>''"
  by(eval)

lemma "eval 1000
            stmt
            (ASSIGN (Id (STR ''a_s120_21_m8'')) (LVAL (Id (STR ''a_s120_21_s8''))))
            (STR ''089Be5381FcEa58aF334101414c04F993947C733'')
            (STR '''')
            (STR ''0'')
            [(STR ''089Be5381FcEa58aF334101414c04F993947C733'', STR ''100'')]
            []
            [((STR ''a_s120_21_s8''), Storage (STArray 1 (STArray 2 (STValue (TSInt 120)))), Stoarr [SArray [SInt 347104507864064359095275590289383142, SInt 565831699297331399489670920129618233]]),
             ((STR ''a_s120_21_m8''), Memory (MTArray 1 (MTArray 2 (MTValue (TSInt 120)))), Memarr [MArray [MInt (290845675805142398428016622247257774), MInt ((-96834026877269277170645294669272226))]])]
= STR ''a_s120_21_m8[0][0]==347104507864064359095275590289383142\<newline>a_s120_21_m8[0][1]==565831699297331399489670920129618233\<newline>a_s120_21_s8[0][0]==347104507864064359095275590289383142\<newline>a_s120_21_s8[0][1]==565831699297331399489670920129618233\<newline>089Be5381FcEa58aF334101414c04F993947C733.balance==100\<newline>''"
  by(eval)

lemma "eval 1000
            stmt
            (ASSIGN (Ref (STR ''a_s8_32_m0'') [UINT 8 1]) (LVAL (Ref (STR ''a_s8_31_s7'') [UINT 8 0]))) 
            (STR ''089Be5381FcEa58aF334101414c04F993947C733'')
            (STR '''')
            (STR ''0'')
            [(STR ''089Be5381FcEa58aF334101414c04F993947C733'', STR ''100'')]
            []
            [(STR ''a_s8_31_s7'', (Storage (STArray 1 (STArray 3 (STValue (TSInt 8)))), Stoarr [SArray [SInt ((98)), SInt ((-23)), SInt (36)]])),
             (STR ''a_s8_32_m0'', (Memory (MTArray 2 (MTArray 3 (MTValue (TSInt 8)))), Memarr [MArray [MInt ((-64)), MInt ((39)), MInt ((-125))], MArray [MInt ((-32)), MInt ((-82)), MInt ((-105))]]))]
       = STR ''a_s8_32_m0[0][0]==-64\<newline>a_s8_32_m0[0][1]==39\<newline>a_s8_32_m0[0][2]==-125\<newline>a_s8_32_m0[1][0]==98\<newline>a_s8_32_m0[1][1]==-23\<newline>a_s8_32_m0[1][2]==36\<newline>a_s8_31_s7[0][0]==98\<newline>a_s8_31_s7[0][1]==-23\<newline>a_s8_31_s7[0][2]==36\<newline>089Be5381FcEa58aF334101414c04F993947C733.balance==100\<newline>''"
  by(eval)


lemma "eval 1000
            stmt
            SKIP
            (STR ''089Be5381FcEa58aF334101414c04F993947C733'')
            (STR '''')
            (STR ''0'')
            [(STR ''089Be5381FcEa58aF334101414c04F993947C733'', STR ''100''), (STR ''115f6e2F70210C14f7DB1AC69737a3CC78435d49'', STR ''100'')]
            []
            [(STR ''v1'', (Storage (STMap (TUInt 32) (STValue (TUInt 8))), Stomap [(STR ''2129136830'', SInt (247))]))]
       = STR ''v1[2129136830]==247\<newline>089Be5381FcEa58aF334101414c04F993947C733.balance==100\<newline>115f6e2F70210C14f7DB1AC69737a3CC78435d49.balance==100\<newline>''"
  by(eval)

value "eval 1000
            stmt
            (INVOKE (STR ''m1'') [])
            (STR ''myaddr'')
            (STR '''')
            (STR ''0'')
            [(STR ''myaddr'', STR ''100'')]
            [
              (STR ''myaddr'',
                ([(STR ''m1'', Method ([], SKIP, None))],
                SKIP))
            ]
            [(STR ''x'', (Value TBool, Stackbool True))]"

lemma "eval 1000
            stmt
            (ASSIGN (Id (STR ''v1'')) (CALL (STR ''m1'') []))
            (STR ''myaddr'')
            (STR '''')
            (STR ''0'')
            [(STR ''myaddr'', STR ''100'')]
            [
              (STR ''myaddr'',
                ([(STR ''m1'', Method ([], SKIP, Some (UINT 8 5)))],
                SKIP))
            ]
            [(STR ''v1'', (Value (TUInt 8), Stackint 0))]
      = STR ''v1==5\<newline>myaddr.balance==100\<newline>''"
  by (eval)

lemma "eval 1000
            stmt
            (ASSIGN (Id (STR ''v1'')) (CALL (STR ''m1'') [E.INT 8 3, E.INT 8 4]))
            (STR ''myaddr'')
            (STR '''')
            (STR ''0'')
            [(STR ''myaddr'', STR ''100'')]
            [
              (STR ''myaddr'',
                ([(STR ''m1'', Method ([(STR ''v2'', Value (TSInt 8)), (STR ''v3'', Value (TSInt 8))], SKIP, Some (PLUS (LVAL (Id (STR ''v2''))) (LVAL (Id (STR ''v3''))))))],
                SKIP))
            ]
            [(STR ''v1'', (Value (TSInt 8), Stackint 0))]
      = STR ''v1==7\<newline>myaddr.balance==100\<newline>''"
  by (eval)

lemma "eval 1000
            stmt
            (ASSIGN (Id (STR ''v1'')) (ECALL (ADDRESS (STR ''extaddr'')) (STR ''m1'') [E.INT 8 3, E.INT 8 4] (E.UINT 8 0)))
            (STR ''myaddr'')
            (STR '''')
            (STR ''0'')
            [(STR ''myaddr'', STR ''100'')]
            [
              (STR ''extaddr'',
                ([(STR ''m1'', Method ([(STR ''v2'', Value (TSInt 8)), (STR ''v3'', Value (TSInt 8))], SKIP, Some (PLUS (LVAL (Id (STR ''v2''))) (LVAL (Id (STR ''v3''))))))],
                SKIP))
            ]
            [(STR ''v1'', (Value (TSInt 8), Stackint 0))]
       = STR ''v1==7\<newline>myaddr.balance==100\<newline>''"
  by (eval)

lemma "eval 1000
            stmt
            (TRANSFER (ADDRESS (STR ''myaddr'')) (UINT 256 10))
            (STR ''089Be5381FcEa58aF334101414c04F993947C733'') 
            (STR '''')
            (STR ''0'')
            [(STR ''089Be5381FcEa58aF334101414c04F993947C733'', STR ''100''), (STR ''0x2d5F6f401c770eEAdd68deB348948ed4504c4676'', STR ''100'')] 
            [
              (STR ''myaddr'',
                ([], SKIP))
            ]
            []
      = STR ''089Be5381FcEa58aF334101414c04F993947C733.balance==90\<newline>0x2d5F6f401c770eEAdd68deB348948ed4504c4676.balance==100\<newline>''"
  by (eval)

value "eval 1000
            stmt
            (TRANSFER (ADDRESS (STR ''myaddr'')) (UINT 256 10))
            (STR ''089Be5381FcEa58aF334101414c04F993947C733'') 
            (STR '''')
            (STR ''0'')
            [(STR ''089Be5381FcEa58aF334101414c04F993947C733'', STR ''100''), (STR ''0x2d5F6f401c770eEAdd68deB348948ed4504c4676'', STR ''100'')] 
            [
              (STR ''myaddr'',
                ([], SKIP))
            ]
            []"

lemma "eval 1000
            stmt
            (COMP(COMP(((ASSIGN (Id (STR ''x''))  (E.UINT 8 0))))(TRANSFER (ADDRESS (STR ''myaddr'')) (UINT 256 5)))(SKIP))
            (STR ''089Be5381FcEa58aF334101414c04F993947C733'')
            (STR '''')
            (STR ''0'')
            [(STR ''089Be5381FcEa58aF334101414c04F993947C733'', STR ''100''), (STR ''115f6e2F70210C14f7DB1AC69737a3CC78435d49'', STR ''100'')]
            [
              (STR ''myaddr'',
                ([], SKIP))
            ]
            [(STR ''x'', (Value (TUInt 8), Stackint 9))]
      = STR ''x==0\<newline>089Be5381FcEa58aF334101414c04F993947C733.balance==95\<newline>115f6e2F70210C14f7DB1AC69737a3CC78435d49.balance==100\<newline>''"
  by (eval)

value "eval 1000
            stmt
            (EXTERNAL (ADDRESS (STR ''Victim'')) (STR ''withdraw'') [] (E.UINT 8 0))
            (STR ''Victim'')
            (STR '''')
            (STR ''0'')
            [(STR ''Victim'', STR ''100''), (STR ''Attacker'', STR ''100'')]
            [
              (STR ''Attacker'',
                [(STR ''withdraw'', Method ([], EXTERNAL (ADDRESS (STR ''Victim'')) (STR ''withdraw'') [] (E.UINT 8 0), None))],
                SKIP),
              (STR ''Victim'',
                [(STR ''withdraw'', Method ([], EXTERNAL (ADDRESS (STR ''Attacker'')) (STR ''withdraw'') [] (E.UINT 8 0), None))],
                SKIP)
            ]
            []"

value "eval 1000
            stmt
            (INVOKE (STR ''withdraw'') [])
            (STR ''Victim'')
            (STR '''')
            (STR ''0'')
            [(STR ''Victim'', STR ''100''), (STR ''Attacker'', STR ''100'')]
            [
              (STR ''Victim'',
                [(STR ''withdraw'', Method ([], INVOKE (STR ''withdraw'') [], None))],
                SKIP)
            ]
            []"

subsection\<open>The Final Code Export\<close>

consts ReadL\<^sub>S   :: "String.literal \<Rightarrow> S"
consts ReadL\<^sub>a\<^sub>c\<^sub>c :: "String.literal \<Rightarrow> (String.literal \<times> String.literal) list"
consts ReadL\<^sub>d\<^sub>a\<^sub>t :: "String.literal \<Rightarrow> (String.literal \<times> Type \<times> Data\<^sub>E\<^sub>n\<^sub>v\<^sub>i\<^sub>r\<^sub>o\<^sub>n\<^sub>m\<^sub>e\<^sub>n\<^sub>t) list"
consts ReadL\<^sub>P :: "String.literal \<Rightarrow> Data\<^sub>P list"

code_printing 
   constant ReadL\<^sub>S  \<rightharpoonup> (Haskell) "Prelude.read"
 | constant ReadL\<^sub>a\<^sub>c\<^sub>c \<rightharpoonup> (Haskell) "Prelude.read"
 | constant ReadL\<^sub>d\<^sub>a\<^sub>t \<rightharpoonup> (Haskell) "Prelude.read"
 | constant ReadL\<^sub>P \<rightharpoonup> (Haskell) "Prelude.read"

fun main_stub :: "String.literal list \<Rightarrow> (int \<times> String.literal)"
  where
   "main_stub [credit, stm, saddr, raddr, val, acc, pr, dat]
        = (0, eval (ReadL\<^sub>n\<^sub>a\<^sub>t credit) stmt (ReadL\<^sub>S stm) saddr raddr val (ReadL\<^sub>a\<^sub>c\<^sub>c acc) (ReadL\<^sub>P pr) (ReadL\<^sub>d\<^sub>a\<^sub>t dat))"
 | "main_stub [stm, saddr, raddr, val, acc, pr, dat]
        = (0, eval 1000 stmt (ReadL\<^sub>S stm) saddr raddr val (ReadL\<^sub>a\<^sub>c\<^sub>c acc) (ReadL\<^sub>P pr) (ReadL\<^sub>d\<^sub>a\<^sub>t dat))"
 | "main_stub _ = (2, 
          STR ''solidity-evaluator [credit] \"Statement\" \"ContractAddress\" \"OriginAddress\" \"Value\"\<newline>''
        + STR ''  \"(Address * Balance) list\" \"(Address * ((Identifier * Member) list) * Statement)\" \"(Variable * Type * Value) list\"\<newline>''
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

export_code eval SKIP main_stub
            in Haskell module_name "Solidity_Evaluator" file_prefix "solidity-evaluator/src"  (string_classes)   

subsection\<open>Demonstrating the Symbolic Execution of Solidity\<close>

abbreviation P1::S
  where "P1 \<equiv> COMP (ASSIGN (Id (STR ''sa'')) (LVAL (Id (STR ''ma''))))
                   (ASSIGN (Ref (STR ''sa'') [UINT (8::nat) 0]) TRUE)"
abbreviation myenv::Environment
  where "myenv \<equiv> updateEnv (STR ''ma'') (Memory (MTArray 1 (MTValue TBool))) (Stackloc (STR ''1''))
                 (updateEnv (STR ''sa'') (Storage (STArray 1 (STValue TBool))) (Storeloc (STR ''1''))
                 (emptyEnv (STR ''ad'') (STR ''ad'') (STR ''0'')))"
 
abbreviation mystack::Stack
  where "mystack \<equiv> updateStore (STR ''1'') (KMemptr (STR ''1'')) emptyStore"
 
abbreviation mystore::StorageT
  where "mystore \<equiv> fmempty"
 
abbreviation mymemory::MemoryT
  where "mymemory \<equiv> updateStore (STR ''0.1'') (MValue (STR ''false'')) emptyStore"
 
abbreviation mystorage::StorageT
  where "mystorage \<equiv> fmupd (STR ''0.1'') (STR ''True'') fmempty"


lemma "( stmt P1 fmempty myenv emptyStore \<lparr>accounts=emptyAccount, stack=mystack, memory=mymemory, storage=fmupd (STR ''ad'') mystorage fmempty, gas=1000\<rparr> ) =
  (Normal ((), \<lparr>accounts=emptyAccount, stack=mystack, memory=mymemory, storage=fmupd (STR ''ad'') mystorage fmempty, gas=1000\<rparr> ))"
  by(solidity_symbex)

end
