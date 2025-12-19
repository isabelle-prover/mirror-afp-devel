section\<open>Storage\<close>

theory Storage
imports Valuetypes "Finite-Map-Extras.Finite_Map_Extras"

begin

subsection \<open>Hashing\<close>

definition hash :: "location \<Rightarrow> String.literal \<Rightarrow> location"
  where "hash loc ix = ix + (STR ''.'' + loc)"

declare hash_def [solidity_symbex]

text \<open>Hash function which uses - for contract version/instance number\<close>
definition hash_version :: "location \<Rightarrow> String.literal \<Rightarrow> location"
  where "hash_version loc ix = ix + (STR ''-'' + loc)"

lemma explode_dot[simp]: "literal.explode STR ''.'' = [CHR ''.'']" 
  by (simp add: Literal.rep_eq zero_literal.rep_eq)

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

subsection \<open>General store\<close>

record 'v store =
  Mapping :: "(location,'v) fmap"
  Toploc :: nat 

definition accessStore :: "location \<Rightarrow> ('a, 'v) store_scheme \<Rightarrow> 'a option"
where "accessStore loc st = fmlookup (Mapping st) loc"

declare accessStore_def[solidity_symbex]

definition emptyStore :: "'v store"
  where "emptyStore = \<lparr> Mapping=fmempty, Toploc=0 \<rparr>"

declare emptyStore_def [solidity_symbex]

definition allocate :: "('a, 'v) store_scheme \<Rightarrow> location * ('a, 'v) store_scheme"
where "allocate s = (let ntop = Suc(Toploc s) in (ShowL\<^sub>n\<^sub>a\<^sub>t ntop, s \<lparr>Toploc := ntop\<rparr>))"


lemma allocateMapping:
  assumes "\<exists>t. (t, s') = allocate s"
  shows "Mapping s = Mapping s'" using assms unfolding allocate_def by auto

lemma accessAllocate:
  assumes "\<exists>t. (t, s') = allocate s"
  shows "\<forall>l. accessStore l s' = accessStore l s" 
  using assms allocateMapping unfolding accessStore_def by force

lemma allocateSameAccess:
  shows "\<forall>loc. accessStore loc m = accessStore loc (snd (allocate m))" 
  unfolding allocate_def accessStore_def by simp


definition updateStore :: "location \<Rightarrow> 'v \<Rightarrow> ('v, 'a) store_scheme \<Rightarrow> ('v, 'a) store_scheme"
where "updateStore loc val s = s \<lparr> Mapping := fmupd loc val (Mapping s)\<rparr>"

declare updateStore_def [solidity_symbex]

lemma accessStore_updateStore[simp]: "accessStore l (updateStore l v st) = Some v" unfolding updateStore_def accessStore_def by auto

lemma accessStore_non_changed:
  assumes "updateStore l v st = st'"
  shows "\<forall>l'. l'\<noteq>l \<longrightarrow> accessStore l' st = accessStore l' st'" 
  using assms unfolding updateStore_def accessStore_def by auto


definition push :: "'v \<Rightarrow> ('v, 'a) store_scheme \<Rightarrow> ('v, 'a) store_scheme"
  where "push val sto = (let s = updateStore (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc sto)) val sto in snd (allocate s))"

declare push_def [solidity_symbex]

subsection \<open>stack\<close>
                                
datatype (discs_sels) stackvalue = KValue valuetype
                    | KCDptr location
                    | KMemptr location
                    | KStoptr location

type_synonym stack = "stackvalue store"

subsection \<open>Storage\<close>

subsubsection \<open>Definition\<close>

type_synonym storagevalue = valuetype

type_synonym storageT = "(location,storagevalue) fmap"

datatype (discs_sels) stypes
  = STArray nat stypes
  | STMap types stypes
  | STValue types

subsubsection \<open>Example\<close>

abbreviation mystorage::storageT
where "mystorage \<equiv> (fmap_of_list
  [(STR ''0.0.0'', STR ''False''),
   (STR ''1.1.0'', STR ''True'')])"

subsubsection \<open>Access storage\<close>

definition accessStorage :: "types \<Rightarrow> location \<Rightarrow> storageT \<Rightarrow> storagevalue"
where
  "accessStorage t loc sto =
    (case sto $$ loc of
      Some v \<Rightarrow> v
    | None \<Rightarrow> ival t)"

declare accessStorage_def [solidity_symbex]

subsubsection \<open>Copy from storage to storage\<close>

primrec copyRec :: "location \<Rightarrow> location \<Rightarrow> stypes \<Rightarrow> storageT \<Rightarrow> storageT option"
where
  "copyRec l\<^sub>s l\<^sub>d (STArray x t) sto =
    iter' (\<lambda>i s'. copyRec (hash l\<^sub>s (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash l\<^sub>d (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t s') sto x"
| "copyRec l\<^sub>s l\<^sub>d (STValue t) sto =
    (let e = accessStorage t l\<^sub>s sto in Some (fmupd l\<^sub>d e sto))"
| "copyRec _ _ (STMap _ _) _ = None"
 
definition copy :: "location \<Rightarrow> location \<Rightarrow> nat \<Rightarrow> stypes \<Rightarrow> storageT \<Rightarrow> storageT option"
where
  "copy l\<^sub>s l\<^sub>d x t sto =
    iter' (\<lambda>i s'. copyRec (hash l\<^sub>s (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash l\<^sub>d (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t s') sto x"

declare copy_def [solidity_symbex]


abbreviation mystorage2::storageT
where "mystorage2 \<equiv> (fmap_of_list
  [(STR ''0.0.0'', STR ''False''),
   (STR ''1.1.0'', STR ''True''),
   (STR ''0.5'', STR ''False''),
   (STR ''1.5'', STR ''True'')])"

lemma "copy (STR ''1.0'') (STR ''5'') 2 (STValue TBool) mystorage = Some mystorage2"
  by eval

subsection \<open>Memory and Calldata\<close>

subsubsection \<open>Definition\<close>

datatype memoryvalue =
  MValue valuetype
  | MPointer location

datatype (discs_sels) mtypes =
  MTArray nat mtypes
  | MTValue types

subsection \<open>Typed Store\<close>

record ('t, 'v) typedstore = "'v store" +
  Typed_Mapping :: "(location, 't) fmap"

text \<open>Use the inherited accessStore for values, add new functions for type management\<close>

definition accessTypeStore :: "location \<Rightarrow> ('t, 'v) typedstore \<Rightarrow> 't option"
where "accessTypeStore loc st = fmlookup (Typed_Mapping st) loc"

declare accessTypeStore_def [solidity_symbex]

definition updateTypeStore :: "location \<Rightarrow> 't \<Rightarrow> ('t, 'v) typedstore \<Rightarrow> ('t, 'v) typedstore"
where "updateTypeStore loc typ st = st \<lparr> Typed_Mapping := fmupd loc typ (Typed_Mapping st) \<rparr>"

declare updateTypeStore_def [solidity_symbex]

definition updateTypedStore :: "location \<Rightarrow> 'v \<Rightarrow> 't \<Rightarrow> ('t, 'v) typedstore \<Rightarrow> ('t, 'v) typedstore"
where "updateTypedStore loc val typ st = updateTypeStore loc typ (updateStore loc val st)"

definition emptyTypedStore :: "('t, 'v) typedstore"
  where "emptyTypedStore = \<lparr> Mapping=fmempty, Toploc=0, Typed_Mapping=fmempty \<rparr>"

declare emptyTypedStore_def [solidity_symbex]

definition pushTyped :: "'v \<Rightarrow> 't \<Rightarrow> ('t, 'v) typedstore \<Rightarrow> ('t, 'v) typedstore"
  where "pushTyped val typ sto = (let s = updateTypedStore (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc sto)) val typ sto in snd (allocate s))"

declare pushTyped_def [solidity_symbex]

lemma "accessStore l (updateTypedStore l v t (emptyTypedStore)) = Some v" 
  unfolding updateTypedStore_def updateTypeStore_def accessStore_def updateStore_def by simp

lemma "accessTypeStore l (updateTypedStore l v t (emptyTypedStore)) = Some t" 
  unfolding updateTypedStore_def updateTypeStore_def accessTypeStore_def updateStore_def by simp

lemma allocateTypeSameAccess:
  shows "\<forall>loc. accessTypeStore loc m = accessTypeStore loc (snd (allocate m))" 
  unfolding allocate_def accessStore_def accessTypeStore_def by simp

type_synonym memoryT = "(mtypes,memoryvalue) typedstore"

type_synonym calldataT = memoryT

subsubsection \<open>Example\<close>

abbreviation mymemory::memoryT
  where "mymemory \<equiv>
    \<lparr>Mapping = fmap_of_list
      [(STR ''1.1.0'', MValue STR ''False''),
       (STR ''0.1.0'', MValue STR ''True''),
       (STR ''1.0'', MPointer STR ''1.0''),
       (STR ''1.0.0'', MValue STR ''False''),
       (STR ''0.0.0'', MValue STR ''True''),
       (STR ''0.0'', MPointer STR ''0.0'')],
     Toploc = 1,
     Typed_Mapping = fmap_of_list
      [(STR ''1.1.0'', MTValue TBool),
       (STR ''0.1.0'', MTValue TBool),
       (STR ''1.0'', MTArray 2 (MTValue TBool)),
       (STR ''1.0.0'', MTValue TBool),
       (STR ''0.0.0'', MTValue TBool),
       (STR ''0.0'', MTArray 2 (MTValue TBool))]\<rparr>"

subsubsection \<open>Initialization\<close>

subsubsection \<open>Definition\<close>

primrec minitRec :: "location \<Rightarrow> mtypes \<Rightarrow> memoryT \<Rightarrow> memoryT"
where
  "minitRec loc (MTArray x t) = (\<lambda>mem.
    let m = updateTypedStore loc (MPointer loc) (MTArray x t) mem
    in iter (\<lambda>i m' . minitRec (hash loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t m') m x)"
| "minitRec loc (MTValue t) = updateTypedStore loc (MValue (ival t)) (MTValue t)"

definition minit :: "nat \<Rightarrow> mtypes \<Rightarrow> memoryT \<Rightarrow> memoryT"
where
  "minit x t mem =
    (let l = ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem);
         m = iter (\<lambda>i m' . minitRec (hash l (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t m') mem x
     in snd (allocate m))"

declare minit_def [solidity_symbex]

primrec arraysGreaterZero::"mtypes \<Rightarrow> bool"
  where "arraysGreaterZero (MTValue v) = True"
       | "arraysGreaterZero (MTArray x t) = (x>0 \<and> arraysGreaterZero t)"

subsubsection \<open>Example\<close>

lemma "minit 2 (MTArray 2 (MTValue TBool)) emptyTypedStore =
\<lparr>Mapping = fmap_of_list
  [(STR ''0.0'', MPointer STR ''0.0''), 
   (STR ''0.0.0'', MValue STR ''False''),
   (STR ''1.0.0'', MValue STR ''False''), 
   (STR ''1.0'', MPointer STR ''1.0''),
   (STR ''0.1.0'', MValue STR ''False''), 
   (STR ''1.1.0'', MValue STR ''False'')],
  Toploc = 1,
  Typed_Mapping = fmap_of_list
  [(STR ''0.0'', MTArray 2 (MTValue TBool)), 
   (STR ''0.0.0'', MTValue TBool),
   (STR ''1.0.0'', MTValue TBool), 
   (STR ''1.0'', MTArray 2 (MTValue TBool)),
   (STR ''0.1.0'', MTValue TBool), 
   (STR ''1.1.0'', MTValue TBool)]\<rparr>" by eval



subsubsection \<open>Copy from memory to memory\<close>

subsubsection \<open>Definition\<close>

primrec cpm2mrec :: "location \<Rightarrow> location \<Rightarrow> mtypes \<Rightarrow> memoryT \<Rightarrow> memoryT \<Rightarrow> memoryT option"
where
  "cpm2mrec l\<^sub>s l\<^sub>d (MTArray x t) m\<^sub>s m\<^sub>d =
    (case accessStore l\<^sub>s m\<^sub>s of
      Some (MPointer l) \<Rightarrow>
        (let m = updateTypedStore l\<^sub>d (MPointer l\<^sub>d) (MTArray x t) m\<^sub>d
          in iter' (\<lambda>i m'. cpm2mrec (hash l (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash l\<^sub>d (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t m\<^sub>s m') m x)
    | _ \<Rightarrow> None)"
| "cpm2mrec l\<^sub>s l\<^sub>d (MTValue t) m\<^sub>s m\<^sub>d =
    (case accessStore l\<^sub>s m\<^sub>s of
      Some (MValue v) \<Rightarrow> Some (updateTypedStore l\<^sub>d (MValue v) (MTValue t) m\<^sub>d)
    | _ \<Rightarrow> None)"

definition cpm2m :: "location \<Rightarrow> location \<Rightarrow> nat \<Rightarrow> mtypes \<Rightarrow> memoryT \<Rightarrow> memoryT \<Rightarrow> memoryT option"
where
  "cpm2m l\<^sub>s l\<^sub>d x t m\<^sub>s m\<^sub>d = iter' (\<lambda>i m. cpm2mrec (hash l\<^sub>s (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash l\<^sub>d (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t m\<^sub>s m) m\<^sub>d x"

declare cpm2m_def [solidity_symbex]

subsubsection \<open>Example\<close>

lemma "cpm2m (STR ''0'') (STR ''0'') 2 (MTArray 2 (MTValue TBool)) mymemory (snd (allocate emptyTypedStore)) = Some mymemory"
  by eval 

abbreviation mymemory2::memoryT
  where "mymemory2 \<equiv>
    \<lparr>Mapping = fmap_of_list
      [(STR ''0.5'', MValue STR ''True''),
       (STR ''1.5'', MValue STR ''False'')],
     Toploc = 0,
     Typed_Mapping = fmap_of_list
      [(STR ''0.5'', MTValue TBool),
       (STR ''1.5'', MTValue TBool)]\<rparr>"

lemma "cpm2m (STR ''1.0'') (STR ''5'') 2 (MTValue TBool) mymemory emptyTypedStore = Some mymemory2" by eval

subsection \<open>Copy from storage to memory\<close>

subsubsection \<open>Definition\<close>

fun cps2mTypeConvert:: "stypes \<Rightarrow> mtypes option"
  where
  "cps2mTypeConvert (STValue t) = Some (MTValue t)"
| "cps2mTypeConvert (STArray len t) = (case (cps2mTypeConvert t) of Some t' \<Rightarrow> Some (MTArray len t')
                                                                   | None \<Rightarrow> None)"
| "cps2mTypeConvert _ = None"

primrec cps2mrec :: "location \<Rightarrow> location \<Rightarrow> stypes \<Rightarrow> storageT \<Rightarrow> memoryT \<Rightarrow> memoryT option"
where
  "cps2mrec locs locm (STArray x t) sto mem =
    (case cps2mTypeConvert t of
      Some t' \<Rightarrow> 
        (let m = updateTypedStore locm (MPointer locm) (MTArray x t') mem
         in iter' (\<lambda>i m'. cps2mrec (hash locs (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash locm (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t sto m') m x)
    | None \<Rightarrow> None)"
| "cps2mrec locs locm (STValue t) sto mem =
    (let v = accessStorage t locs sto
    in Some (updateTypedStore locm (MValue v) (MTValue t) mem))"
| "cps2mrec _ _ (STMap _ _) _ _ = None"

definition cps2m :: "location \<Rightarrow> location \<Rightarrow> nat \<Rightarrow> stypes \<Rightarrow> storageT \<Rightarrow> memoryT \<Rightarrow> memoryT option"
where
  "cps2m locs locm x t sto mem =
    iter' (\<lambda>i m'. cps2mrec (hash locs (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash locm (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t sto m') mem x"

declare cps2m_def [solidity_symbex]

subsubsection \<open>Example\<close>

abbreviation mystorage3::storageT
where "mystorage3 \<equiv> (fmap_of_list
  [(STR ''0.0.1'', STR ''True''),
   (STR ''1.0.1'', STR ''False''),
   (STR ''0.1.1'', STR ''True''),
   (STR ''1.1.1'', STR ''False'')])"

lemma "cps2m (STR ''1'') (STR ''0'') 2 (STArray 2 (STValue TBool)) mystorage3 (snd (allocate emptyTypedStore)) = Some mymemory"
  by eval

fun cps2mTypeCompatible:: "stypes \<Rightarrow> mtypes \<Rightarrow> bool"
  where
  "cps2mTypeCompatible (STValue t) (MTValue t') = (t = t')"
| "cps2mTypeCompatible (STArray len t) (MTArray len' t') = (len' > 0 \<and> len = len' \<and> cps2mTypeCompatible t t')"
| "cps2mTypeCompatible _ _ = False"

subsection \<open>Copy from memory to storage\<close>

subsubsection \<open>Definition\<close>
primrec cpm2srec :: "location \<Rightarrow> location \<Rightarrow> mtypes \<Rightarrow> memoryT \<Rightarrow> storageT \<Rightarrow> storageT option"
where
  "cpm2srec locm locs (MTArray x t) mem sto =
    (case accessStore locm mem of
      Some (MPointer l) \<Rightarrow>
        iter' (\<lambda>i s'. cpm2srec (hash l (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash locs (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t mem s') sto x
    | _ \<Rightarrow> None)"
| "cpm2srec locm locs (MTValue t) mem sto =
    (case accessStore locm mem of
      Some (MValue v) \<Rightarrow> Some (fmupd locs v sto)
    | _ \<Rightarrow> None)"

definition cpm2s :: "location \<Rightarrow> location \<Rightarrow> nat \<Rightarrow> mtypes \<Rightarrow> memoryT \<Rightarrow> storageT \<Rightarrow> storageT option"
where
  "cpm2s locm locs x t mem sto =
    iter' (\<lambda>i s'. cpm2srec (hash locm (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash locs (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t mem s') sto x"

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
