section\<open>Storage\<close>

theory Storage
imports Valuetypes "Finite-Map-Extras.Finite_Map_Extras"

begin

subsection \<open>Hashing\<close>

definition hash :: "Location \<Rightarrow> String.literal \<Rightarrow> Location"
  where "hash loc ix = ix + (STR ''.'' + loc)"

declare hash_def [solidity_symbex]

lemma example: "hash (STR ''1.0'') (STR ''2'') = hash (STR ''0'') (STR ''2.1'')" by eval

lemma hash_explode:
  "String.explode (hash l i) = String.explode i @ (String.explode (STR ''.'') @ String.explode l)"
  unfolding hash_def by (simp add: plus_literal.rep_eq)

lemma hash_dot:
  "String.explode (hash l i) ! length (String.explode i) = CHR ''.''"
  unfolding hash_def by (simp add: Literal.rep_eq plus_literal.rep_eq)

lemma hash_injective:
  assumes "hash l i = hash l' i'"
    and "CHR ''.'' \<notin> set (String.explode i)"
    and "CHR ''.'' \<notin> set (String.explode i')"
  shows "l = l' \<and> i = i'"
proof (rule ccontr)
  assume "\<not> (l = l' \<and> i = i')" 
  then consider (1) "i\<noteq>i'" | (2) "i=i' \<and> l\<noteq>l'" by auto
  then have "String.explode (hash l i) \<noteq> String.explode (hash l' i')"
  proof cases
    case 1
    then have neq: "(String.explode i) \<noteq> (String.explode i')" by (metis literal.explode_inverse)

    consider (1) "length (String.explode i) = length (String.explode i')" | (2) "length (String.explode i) < length (String.explode i')" | (3) "length (String.explode i) > length (String.explode i')" by linarith
    then show ?thesis
    proof (cases)
      case 1
      then obtain j where "String.explode i ! j \<noteq> String.explode i' ! j" using neq nth_equalityI by auto
      then show ?thesis using 1 plus_literal.rep_eq unfolding hash_def by force
    next
      case 2
      then have "String.explode i' ! length (String.explode i) \<noteq> CHR ''.''" using assms(3) by (metis nth_mem)
      then have "String.explode (hash l' i') ! length (String.explode i) \<noteq> CHR ''.''" using 2 hash_explode[of l' i'] by (simp add: nth_append)
      moreover have "String.explode (hash l i) ! length (String.explode i) = CHR ''.''" using hash_dot by simp
      ultimately show ?thesis by auto
    next
      case 3
      then have "String.explode i ! length (String.explode i') \<noteq> CHR ''.''" using assms(2) by (metis nth_mem)
      then have "String.explode (hash l i) ! length (String.explode i') \<noteq> CHR ''.''" using 3 hash_explode[of l i] by (simp add: nth_append)
      moreover have "String.explode (hash l' i') ! length (String.explode i') = CHR ''.''" using hash_dot by simp
      ultimately show ?thesis by auto
    qed
  next
    case 2
    then show ?thesis using hash_explode literal.explode_inject by force
  qed
  then show False using assms(1) by simp
qed

subsection \<open>General Store\<close>

record 'v Store =
  mapping :: "(Location,'v) fmap"
  toploc :: nat 

definition accessStore :: "Location \<Rightarrow> 'v Store \<Rightarrow> 'v option"
where "accessStore loc st = fmlookup (mapping st) loc"

declare accessStore_def[solidity_symbex]

definition emptyStore :: "'v Store"
where "emptyStore = \<lparr> mapping=fmempty, toploc=0 \<rparr>"

declare emptyStore_def [solidity_symbex]

definition allocate :: "'v Store \<Rightarrow> Location * ('v Store)"
where "allocate s = (let ntop = Suc(toploc s) in (ShowL\<^sub>n\<^sub>a\<^sub>t ntop, s \<lparr>toploc := ntop\<rparr>))"



definition updateStore :: "Location \<Rightarrow> 'v \<Rightarrow> 'v Store \<Rightarrow> 'v Store"
where "updateStore loc val s = s \<lparr> mapping := fmupd loc val (mapping s)\<rparr>"

declare updateStore_def [solidity_symbex]

definition push :: "'v \<Rightarrow> 'v Store \<Rightarrow> 'v Store"
  where "push val sto = (let s = updateStore (ShowL\<^sub>n\<^sub>a\<^sub>t (toploc sto)) val sto in snd (allocate s))"

declare push_def [solidity_symbex]

subsection \<open>Stack\<close>

datatype Stackvalue = KValue Valuetype
                    | KCDptr Location
                    | KMemptr Location
                    | KStoptr Location

type_synonym Stack = "Stackvalue Store"

subsection \<open>Storage\<close>

subsubsection \<open>Definition\<close>

type_synonym Storagevalue = Valuetype

type_synonym StorageT = "(Location,Storagevalue) fmap"

datatype STypes = STArray int STypes
                | STMap Types STypes
                | STValue Types

subsubsection \<open>Example\<close>

abbreviation mystorage::StorageT
where "mystorage \<equiv> (fmap_of_list
  [(STR ''0.0.0'', STR ''False''),
   (STR ''1.1.0'', STR ''True'')])"

subsubsection \<open>Access storage\<close>

definition accessStorage :: "Types \<Rightarrow> Location \<Rightarrow> StorageT \<Rightarrow> Storagevalue"
where
  "accessStorage t loc sto =
    (case sto $$ loc of
      Some v \<Rightarrow> v
    | None \<Rightarrow> ival t)"

declare accessStorage_def [solidity_symbex]

subsubsection \<open>Copy from storage to storage\<close>

primrec copyRec :: "Location \<Rightarrow> Location \<Rightarrow> STypes \<Rightarrow> StorageT \<Rightarrow> StorageT option"
where
  "copyRec l\<^sub>s l\<^sub>d (STArray x t) sto =
    iter' (\<lambda>i s'. copyRec (hash l\<^sub>s (ShowL\<^sub>i\<^sub>n\<^sub>t i)) (hash l\<^sub>d (ShowL\<^sub>i\<^sub>n\<^sub>t i)) t s') sto x"
| "copyRec l\<^sub>s l\<^sub>d (STValue t) sto =
    (let e = accessStorage t l\<^sub>s sto in Some (fmupd l\<^sub>d e sto))"
| "copyRec _ _ (STMap _ _) _ = None"
 
definition copy :: "Location \<Rightarrow> Location \<Rightarrow> int \<Rightarrow> STypes \<Rightarrow> StorageT \<Rightarrow> StorageT option"
where
  "copy l\<^sub>s l\<^sub>d x t sto =
    iter' (\<lambda>i s'. copyRec (hash l\<^sub>s (ShowL\<^sub>i\<^sub>n\<^sub>t i)) (hash l\<^sub>d (ShowL\<^sub>i\<^sub>n\<^sub>t i)) t s') sto x"

declare copy_def [solidity_symbex]


abbreviation mystorage2::StorageT
where "mystorage2 \<equiv> (fmap_of_list
  [(STR ''0.0.0'', STR ''False''),
   (STR ''1.1.0'', STR ''True''),
   (STR ''0.5'', STR ''False''),
   (STR ''1.5'', STR ''True'')])"

lemma "copy (STR ''1.0'') (STR ''5'') 2 (STValue TBool) mystorage = Some mystorage2"
  by eval

subsection \<open>Memory and Calldata\<close>

subsubsection \<open>Definition\<close>

datatype Memoryvalue =
  MValue Valuetype
  | MPointer Location

type_synonym MemoryT = "Memoryvalue Store"

type_synonym CalldataT = MemoryT

datatype MTypes =
  MTArray int MTypes
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

primrec minitRec :: "Location \<Rightarrow> MTypes \<Rightarrow> MemoryT \<Rightarrow> MemoryT"
where
  "minitRec loc (MTArray x t) = (\<lambda>mem.
    let m = updateStore loc (MPointer loc) mem
    in iter (\<lambda>i m' . minitRec (hash loc (ShowL\<^sub>i\<^sub>n\<^sub>t i)) t m') m x)"
| "minitRec loc (MTValue t) = updateStore loc (MValue (ival t))"

definition minit :: "int \<Rightarrow> MTypes \<Rightarrow> MemoryT \<Rightarrow> MemoryT"
where
  "minit x t mem =
    (let l = ShowL\<^sub>n\<^sub>a\<^sub>t (toploc mem);
         m = iter (\<lambda>i m' . minitRec (hash l (ShowL\<^sub>i\<^sub>n\<^sub>t i)) t m') mem x
     in snd (allocate m))"

declare minit_def [solidity_symbex]

subsubsection \<open>Example\<close>

lemma "minit 2 (MTArray 2 (MTValue TBool)) emptyStore =
\<lparr>mapping = fmap_of_list
  [(STR ''0.0'', MPointer STR ''0.0''), (STR ''0.0.0'', MValue STR ''False''),
   (STR ''1.0.0'', MValue STR ''False''), (STR ''1.0'', MPointer STR ''1.0''),
   (STR ''0.1.0'', MValue STR ''False''), (STR ''1.1.0'', MValue STR ''False'')],
  toploc = 1\<rparr>" by eval

subsubsection \<open>Copy from memory to memory\<close>

subsubsection \<open>Definition\<close>

primrec cpm2mrec :: "Location \<Rightarrow> Location \<Rightarrow> MTypes \<Rightarrow> MemoryT \<Rightarrow> MemoryT \<Rightarrow> MemoryT option"
where
  "cpm2mrec l\<^sub>s l\<^sub>d (MTArray x t) m\<^sub>s m\<^sub>d =
    (case accessStore l\<^sub>s m\<^sub>s of
      Some (MPointer l) \<Rightarrow>
        (let m = updateStore l\<^sub>d (MPointer l\<^sub>d) m\<^sub>d
          in iter' (\<lambda>i m'. cpm2mrec (hash l\<^sub>s (ShowL\<^sub>i\<^sub>n\<^sub>t i)) (hash l\<^sub>d (ShowL\<^sub>i\<^sub>n\<^sub>t i)) t m\<^sub>s m') m x)
    | _ \<Rightarrow> None)"
| "cpm2mrec l\<^sub>s l\<^sub>d (MTValue t) m\<^sub>s m\<^sub>d =
    (case accessStore l\<^sub>s m\<^sub>s of
      Some (MValue v) \<Rightarrow> Some (updateStore l\<^sub>d (MValue v) m\<^sub>d)
    | _ \<Rightarrow> None)"

definition cpm2m :: "Location \<Rightarrow> Location \<Rightarrow> int \<Rightarrow> MTypes \<Rightarrow> MemoryT \<Rightarrow> MemoryT \<Rightarrow> MemoryT option"
where
  "cpm2m l\<^sub>s l\<^sub>d x t m\<^sub>s m\<^sub>d = iter' (\<lambda>i m. cpm2mrec (hash l\<^sub>s (ShowL\<^sub>i\<^sub>n\<^sub>t i)) (hash l\<^sub>d (ShowL\<^sub>i\<^sub>n\<^sub>t i)) t m\<^sub>s m) m\<^sub>d x"

declare cpm2m_def [solidity_symbex]

subsubsection \<open>Example\<close>

lemma "cpm2m (STR ''0'') (STR ''0'') 2 (MTArray 2 (MTValue TBool)) mymemory (snd (allocate emptyStore)) = Some mymemory"
  by eval

abbreviation mymemory2::MemoryT
  where "mymemory2 \<equiv>
    \<lparr>mapping = fmap_of_list
      [(STR ''0.5'', MValue STR ''True''),
       (STR ''1.5'', MValue STR ''False'')],
     toploc = 0\<rparr>"

lemma "cpm2m (STR ''1.0'') (STR ''5'') 2 (MTValue TBool) mymemory emptyStore = Some mymemory2" by eval

subsection \<open>Copy from storage to memory\<close>

subsubsection \<open>Definition\<close>

primrec cps2mrec :: "Location \<Rightarrow> Location \<Rightarrow> STypes \<Rightarrow> StorageT \<Rightarrow> MemoryT \<Rightarrow> MemoryT option"
where
  "cps2mrec locs locm (STArray x t) sto mem =
    (let m = updateStore locm (MPointer locm) mem
    in iter' (\<lambda>i m'. cps2mrec (hash locs (ShowL\<^sub>i\<^sub>n\<^sub>t i)) (hash locm (ShowL\<^sub>i\<^sub>n\<^sub>t i)) t sto m') m x)"
| "cps2mrec locs locm (STValue t) sto mem =
    (let v = accessStorage t locs sto
    in Some (updateStore locm (MValue v) mem))"
| "cps2mrec _ _ (STMap _ _) _ _ = None"

definition cps2m :: "Location \<Rightarrow> Location \<Rightarrow> int \<Rightarrow> STypes \<Rightarrow> StorageT \<Rightarrow> MemoryT \<Rightarrow> MemoryT option"
where
  "cps2m locs locm x t sto mem =
    iter' (\<lambda>i m'. cps2mrec (hash locs (ShowL\<^sub>i\<^sub>n\<^sub>t i)) (hash locm (ShowL\<^sub>i\<^sub>n\<^sub>t i)) t sto m') mem x"

declare cps2m_def [solidity_symbex]

subsubsection \<open>Example\<close>

abbreviation mystorage3::StorageT
where "mystorage3 \<equiv> (fmap_of_list
  [(STR ''0.0.1'', STR ''True''),
   (STR ''1.0.1'', STR ''False''),
   (STR ''0.1.1'', STR ''True''),
   (STR ''1.1.1'', STR ''False'')])"

lemma "cps2m (STR ''1'') (STR ''0'') 2 (STArray 2 (STValue TBool)) mystorage3 (snd (allocate emptyStore)) = Some mymemory"
  by eval

subsection \<open>Copy from memory to storage\<close>

subsubsection \<open>Definition\<close>

primrec cpm2srec :: "Location \<Rightarrow> Location \<Rightarrow> MTypes \<Rightarrow> MemoryT \<Rightarrow> StorageT \<Rightarrow> StorageT option"
where
  "cpm2srec locm locs (MTArray x t) mem sto =
    (case accessStore locm mem of
      Some (MPointer l) \<Rightarrow>
        iter' (\<lambda>i s'. cpm2srec (hash locm (ShowL\<^sub>i\<^sub>n\<^sub>t i)) (hash locs (ShowL\<^sub>i\<^sub>n\<^sub>t i)) t mem s') sto x
    | _ \<Rightarrow> None)"
| "cpm2srec locm locs (MTValue t) mem sto =
    (case accessStore locm mem of
      Some (MValue v) \<Rightarrow> Some (fmupd locs v sto)
    | _ \<Rightarrow> None)"

definition cpm2s :: "Location \<Rightarrow> Location \<Rightarrow> int \<Rightarrow> MTypes \<Rightarrow> MemoryT \<Rightarrow> StorageT \<Rightarrow> StorageT option"
where
  "cpm2s locm locs x t mem sto =
    iter' (\<lambda>i s'. cpm2srec (hash locm (ShowL\<^sub>i\<^sub>n\<^sub>t i)) (hash locs (ShowL\<^sub>i\<^sub>n\<^sub>t i)) t mem s') sto x"

declare cpm2s_def [solidity_symbex]

subsubsection \<open>Example\<close>

lemma "cpm2s (STR ''0'') (STR ''1'') 2 (MTArray 2 (MTValue TBool)) mymemory fmempty = Some mystorage3"
  by eval

declare copyRec.simps [simp del, solidity_symbex add]
declare minitRec.simps [simp del, solidity_symbex add]
declare cpm2mrec.simps [simp del, solidity_symbex add]
declare cps2mrec.simps [simp del, solidity_symbex add]
declare cpm2srec.simps [simp del, solidity_symbex add]

end
