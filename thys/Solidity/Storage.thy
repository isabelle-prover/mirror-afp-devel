section\<open>Storage\<close>

theory Storage
imports Valuetypes "HOL-Library.Finite_Map"

begin

(*Covered*)
fun hash :: "Location \<Rightarrow> String.literal \<Rightarrow> Location"
where "hash loc ix = ix + (STR ''.'' + loc)"

subsection \<open>General Store\<close>

(*Covered*)
record 'v Store =
  mapping :: "(Location,'v) fmap"
  toploc :: nat 

fun accessStore :: "Location \<Rightarrow> 'v Store \<Rightarrow> 'v option"
where "accessStore loc st = fmlookup (mapping st) loc"

definition emptyStore :: "'v Store"
where "emptyStore = \<lparr> mapping=fmempty, toploc=0 \<rparr>"

declare emptyStore_def [solidity_symbex]

fun allocate :: "'v Store \<Rightarrow> Location * ('v Store)"
where "allocate s = (let ntop = Suc(toploc s) in (ShowL\<^sub>n\<^sub>a\<^sub>t ntop, s \<lparr>toploc := ntop\<rparr>))"

fun updateStore :: "Location \<Rightarrow> 'v \<Rightarrow> 'v Store \<Rightarrow> 'v Store"
where "updateStore loc val s = s \<lparr> mapping := fmupd loc val (mapping s)\<rparr>"

fun push :: "'v \<Rightarrow> 'v Store \<Rightarrow> 'v Store"
  where "push val sto = (let s = updateStore (ShowL\<^sub>n\<^sub>a\<^sub>t (toploc sto)) val sto in snd (allocate s))"

subsection \<open>Stack\<close>
(*Covered*)
datatype Stackvalue = KValue Valuetype
                    | KCDptr Location
                    | KMemptr Location
                    | KStoptr Location

(*Covered*)
type_synonym Stack = "Stackvalue Store"

subsection \<open>Storage\<close>

subsubsection \<open>Definition\<close>

type_synonym Storagevalue = Valuetype

(*Covered*)
type_synonym StorageT = "(Location,Storagevalue) fmap"

(*Covered*)
datatype STypes = STArray int STypes
                | STMap Types STypes
                | STValue Types

subsubsection \<open>Example\<close>

abbreviation mystorage::StorageT
where "mystorage \<equiv> (fmap_of_list
  [(STR ''0.0.1'', STR ''True''),
   (STR ''1.0.1'', STR ''False''),
   (STR ''0.1.1'', STR ''True''),
   (STR ''1.1.1'', STR ''False'')])"

subsubsection \<open>Access storage\<close>

(*Covered*)
fun accessStorage :: "Types \<Rightarrow> Location \<Rightarrow> StorageT \<Rightarrow> Storagevalue"
where
  "accessStorage t loc sto =
    (case fmlookup sto loc of
      Some v \<Rightarrow> v
    | None \<Rightarrow> ival t)"

subsubsection \<open>Copy from storage to storage\<close>

fun copyRec :: "Location \<Rightarrow> Location \<Rightarrow> STypes \<Rightarrow> StorageT \<Rightarrow> StorageT option"
where
  "copyRec loc loc' (STArray x t) sto =
    iter' (\<lambda>i s'. copyRec (hash loc (ShowL\<^sub>i\<^sub>n\<^sub>t i)) (hash loc' (ShowL\<^sub>i\<^sub>n\<^sub>t i)) t s') sto x"
| "copyRec loc loc' (STValue t) sto =
    (let e = accessStorage t loc sto in Some (fmupd loc' e sto))"
| "copyRec _ _ (STMap _ _) _ = None"
 
fun copy :: "Location \<Rightarrow> Location \<Rightarrow> int \<Rightarrow> STypes \<Rightarrow> StorageT \<Rightarrow> StorageT option"
where
  "copy loc loc' x t sto =
    iter' (\<lambda>i s'. copyRec (hash loc (ShowL\<^sub>i\<^sub>n\<^sub>t i)) (hash loc' (ShowL\<^sub>i\<^sub>n\<^sub>t i)) t s') sto x"

subsection \<open>Memory and Calldata\<close>

subsubsection \<open>Definition\<close>

(*Covered*)
datatype Memoryvalue =
  MValue Valuetype
  | MPointer Location
(*Covered*)
type_synonym MemoryT = "Memoryvalue Store"
(*Covered*)
type_synonym CalldataT = MemoryT
(*Covered*)
datatype MTypes = MTArray int MTypes
  | MTValue Types

subsubsection \<open>Example\<close>

abbreviation mymemory::MemoryT
  where "mymemory \<equiv>
    \<lparr>mapping = fmap_of_list
      [(STR ''1.1.0'', MValue STR ''False''),
       (STR ''0.1.0'', MValue STR ''True''),
       (STR ''1.0'', MPointer STR ''1.0''),
       (STR ''1.0.0'', MValue STR ''False''),
       (STR ''0.0.0'', MValue STR ''True''),
       (STR ''0.0'', MPointer STR ''0.0'')],
     toploc = 1\<rparr>"

subsubsection \<open>Initialization\<close>

subsubsection \<open>Definition\<close>

(*Covered*)
fun minitRec :: "Location \<Rightarrow> MTypes \<Rightarrow> MemoryT \<Rightarrow> MemoryT"
where
  "minitRec loc (MTArray x t) = (\<lambda>mem.
    let m = updateStore loc (MPointer loc) mem
    in iter (\<lambda>i m' . minitRec (hash loc (ShowL\<^sub>i\<^sub>n\<^sub>t i)) t m') m x)"
| "minitRec loc (MTValue t) = updateStore loc (MValue (ival t))"

(*Covered*)
fun minit :: "int \<Rightarrow> MTypes \<Rightarrow> MemoryT \<Rightarrow> MemoryT"
where
  "minit x t mem =
    (let l = ShowL\<^sub>n\<^sub>a\<^sub>t (toploc mem);
         m = iter (\<lambda>i m' . minitRec (hash l (ShowL\<^sub>i\<^sub>n\<^sub>t i)) t m') mem x
     in snd (allocate m))"

subsubsection \<open>Example\<close>

lemma "minit 2 (MTArray 2 (MTValue TBool)) emptyStore =
\<lparr>mapping = fmap_of_list
  [(STR ''0.0'', MPointer STR ''0.0''), (STR ''0.0.0'', MValue STR ''False''),
   (STR ''1.0.0'', MValue STR ''False''), (STR ''1.0'', MPointer STR ''1.0''),
   (STR ''0.1.0'', MValue STR ''False''), (STR ''1.1.0'', MValue STR ''False'')],
  toploc = 1\<rparr>" by eval

subsubsection \<open>Copy from memory to memory\<close>

subsubsection \<open>Definition\<close>

fun cpm2mrec :: "Location \<Rightarrow> Location \<Rightarrow> MTypes \<Rightarrow> MemoryT \<Rightarrow> MemoryT \<Rightarrow> MemoryT option"
where
  "cpm2mrec l\<^sub>s l\<^sub>d (MTArray x t) m\<^sub>s m\<^sub>d =
    (case accessStore l\<^sub>s m\<^sub>s of
      Some e \<Rightarrow>
        (case e of
          MPointer l \<Rightarrow> (let m = updateStore l\<^sub>d (MPointer l\<^sub>d) m\<^sub>d
             in iter' (\<lambda>i m'. cpm2mrec (hash l\<^sub>s (ShowL\<^sub>i\<^sub>n\<^sub>t i)) (hash l\<^sub>d (ShowL\<^sub>i\<^sub>n\<^sub>t i)) t m\<^sub>s m') m x)
        | _ \<Rightarrow> None)
    | None \<Rightarrow> None)"
| "cpm2mrec l\<^sub>s l\<^sub>d (MTValue t) m\<^sub>s m\<^sub>d =
    (case accessStore l\<^sub>s m\<^sub>s of
      Some e \<Rightarrow> (case e of
          MValue v \<Rightarrow> Some (updateStore l\<^sub>d (MValue v) m\<^sub>d)
        | _ \<Rightarrow> None)
    | None \<Rightarrow> None)"
 
fun cpm2m :: "Location \<Rightarrow> Location \<Rightarrow> int \<Rightarrow> MTypes \<Rightarrow> MemoryT \<Rightarrow> MemoryT \<Rightarrow> MemoryT option"
where
  "cpm2m l\<^sub>s l\<^sub>d x t m\<^sub>s m\<^sub>d = iter' (\<lambda>i m. cpm2mrec (hash l\<^sub>s (ShowL\<^sub>i\<^sub>n\<^sub>t i)) (hash l\<^sub>d (ShowL\<^sub>i\<^sub>n\<^sub>t i)) t m\<^sub>s m) m\<^sub>d x"

subsubsection \<open>Example\<close>

lemma "cpm2m (STR ''0'') (STR ''0'') 2 (MTArray 2 (MTValue TBool)) mymemory (snd (allocate emptyStore)) = Some mymemory"
  by eval

subsection \<open>Copy from storage to memory\<close>

subsubsection \<open>Definition\<close>

(*Covered*)
fun cps2mrec :: "Location \<Rightarrow> Location \<Rightarrow> STypes \<Rightarrow> StorageT \<Rightarrow> MemoryT \<Rightarrow> MemoryT option"
where
  "cps2mrec locs locm (STArray x t) sto mem =
    (let m = updateStore locm (MPointer locm) mem
    in iter' (\<lambda>i m'. cps2mrec (hash locs (ShowL\<^sub>i\<^sub>n\<^sub>t i)) (hash locm (ShowL\<^sub>i\<^sub>n\<^sub>t i)) t sto m') m x)"
| "cps2mrec locs locm (STValue t) sto mem =
    (let v = accessStorage t locs sto
    in Some (updateStore locm (MValue v) mem))"
| "cps2mrec _ _ (STMap _ _) _ _ = None"

(*Covered*)
fun cps2m :: "Location \<Rightarrow> Location \<Rightarrow> int \<Rightarrow> STypes \<Rightarrow> StorageT \<Rightarrow> MemoryT \<Rightarrow> MemoryT option"
where
  "cps2m locs locm x t sto mem =
    iter' (\<lambda>i m'. cps2mrec (hash locs (ShowL\<^sub>i\<^sub>n\<^sub>t i)) (hash locm (ShowL\<^sub>i\<^sub>n\<^sub>t i)) t sto m') mem x"

subsubsection \<open>Example\<close>

lemma "cps2m (STR ''1'') (STR ''0'') 2 (STArray 2 (STValue TBool)) mystorage (snd (allocate emptyStore)) = Some mymemory"
  by eval

subsection \<open>Copy from memory to storage\<close>

subsubsection \<open>Definition\<close>

(*covered*)
fun cpm2srec :: "Location \<Rightarrow> Location \<Rightarrow> MTypes \<Rightarrow> MemoryT \<Rightarrow> StorageT \<Rightarrow> StorageT option"
where
  "cpm2srec locm locs (MTArray x t) mem sto =
    (case accessStore locm mem of
      Some e \<Rightarrow>
        (case e of
          MPointer l \<Rightarrow> iter' (\<lambda>i s'. cpm2srec (hash locm (ShowL\<^sub>i\<^sub>n\<^sub>t i)) (hash locs (ShowL\<^sub>i\<^sub>n\<^sub>t i)) t mem s') sto x
        | _ \<Rightarrow> None)
    | None \<Rightarrow> None)"
| "cpm2srec locm locs (MTValue t) mem sto =
    (case accessStore locm mem of
      Some e \<Rightarrow> (case e of
          MValue v \<Rightarrow> Some (fmupd locs v sto)
        | _ \<Rightarrow> None)
    | None \<Rightarrow> None)"

(*covered*)
fun cpm2s :: "Location \<Rightarrow> Location \<Rightarrow> int \<Rightarrow> MTypes \<Rightarrow> MemoryT \<Rightarrow> StorageT \<Rightarrow> StorageT option"
where
  "cpm2s locm locs x t mem sto =
    iter' (\<lambda>i s'. cpm2srec (hash locm (ShowL\<^sub>i\<^sub>n\<^sub>t i)) (hash locs (ShowL\<^sub>i\<^sub>n\<^sub>t i)) t mem s') sto x"

subsubsection \<open>Example\<close>

lemma "cpm2s (STR ''0'') (STR ''1'') 2 (MTArray 2 (MTValue TBool)) mymemory fmempty = Some mystorage"
  by eval

end
