
theory Dali
  imports "HOL-CSPM" "HOL-CSP.GenFixrec-HOLCF"
begin

text \<open> This model is based on the IFM 2025 Article: 
"Model-Checking Buffered Durable Linearizability in CSP" by 
Edmonds, C., Derrick, J., Dongol, B., Schellhorn, G., Wehrheim, H.

A Zenodo Distribution on  the sources can be found under:
\<^url>\<open>https://zenodo.org/records/15041794\<close>.

Meanwhile, a corrigendum appeared.
\<close>

type_synonym NodeIds = nat
type_synonym Keys    = nat
type_synonym Pointer = nat
type_synonym Values  = nat   (* better completely parametric ? 'a ?? *)
type_synonym Tids    = nat
type_synonym Epoches = nat

text\<open>The data of the model are indexed by natural numbers; their ranges are bounded by the
parameters of the locale \<open>Dali\<close> below (instead of an ad-hoc finitization by enumeration types).\<close>

datatype NodeIDType      = Null | N NodeIds
datatype KeyType         = K Keys
datatype Pointers        = Bot | P Pointer
datatype ValType         = TNull | V Values
datatype ThreadID        = Th Tids
datatype BucketEpochType = BE Epoches

text\<open>Names for the first elements, as in the original (finite) model:\<close>

abbreviation \<open>N0 \<equiv> N 0\<close>    abbreviation \<open>N1 \<equiv> N 1\<close>    abbreviation \<open>N2 \<equiv> N 2\<close>
abbreviation \<open>K0 \<equiv> K 0\<close>    abbreviation \<open>K1 \<equiv> K 1\<close>
abbreviation \<open>P0 \<equiv> P 0\<close>    abbreviation \<open>P1 \<equiv> P 1\<close>    abbreviation \<open>P2 \<equiv> P 2\<close>
abbreviation \<open>V0 \<equiv> V 0\<close>    abbreviation \<open>V1 \<equiv> V 1\<close>
abbreviation \<open>T0 \<equiv> Th 0\<close>   abbreviation \<open>T1 \<equiv> Th 1\<close>   abbreviation \<open>T2 \<equiv> Th 2\<close>
abbreviation \<open>BE0 \<equiv> BE 0\<close>  abbreviation \<open>BE1 \<equiv> BE 1\<close>  abbreviation \<open>BE2 \<equiv> BE 2\<close>

datatype channels = initNode \<open>NodeIDType \<times> KeyType \<times> ValType\<close>
  | getVal \<open>NodeIDType \<times> ValType\<close>
  | getKey \<open>NodeIDType \<times> KeyType\<close>
  | getNext \<open>NodeIDType \<times> NodeIDType\<close>
  | setNext \<open>NodeIDType \<times> NodeIDType\<close>
  | noFreeNode
  | persistNode NodeIDType
  | crash

  | setPointerNode \<open>Pointers \<times> NodeIDType\<close>
  | getPointerNode \<open>Pointers \<times> NodeIDType\<close>

  | getActiveNode Pointers
  | getCommittedNode Pointers
  | getFlightNode Pointers
  | getBucketEpoch BucketEpochType
  | setStat \<open>Pointers \<times> Pointers \<times> Pointers \<times> BucketEpochType\<close>

  | lock
  | unlock

  | invRead \<open>ThreadID \<times> KeyType\<close>
  | resRead \<open>ThreadID \<times> ValType\<close>

  | invUpdate \<open>ThreadID \<times> KeyType \<times> ValType\<close>
  | resUpdate ThreadID
  | resUpdateFull ThreadID

  | getGlobalEpoch \<open>ThreadID \<times> BucketEpochType\<close>
  | getGlobalEpochW BucketEpochType
  | incGlobalEpoch
  | persistGlobalEpoch
  | setEpochLock bool

  | addFailure BucketEpochType
  | persistFailureList
  | ssFail \<open>BucketEpochType \<times> bool\<close>

  | getTIDTransaction \<open>ThreadID \<times> BucketEpochType\<close>

  | pickFreeTID ThreadID

  | doRead \<open>ThreadID \<times> KeyType \<times> ValType\<close>
  | doUpdate \<open>ThreadID \<times> KeyType \<times> ValType\<close>
  | doUpdateFull ThreadID
  | persist
  | getUsedThreads \<open>ThreadID set\<close>

 


section \<open>Auxiliaries: Traces and Hiding in the Traces Model\<close>

text\<open>FDR checks trace assertions in the traces model, where hiding is just the projection of
traces; divergence is irrelevant there. \<open>traces_hiding\<close> captures this notion of hiding.\<close>

lemma replicate_setinterleaves: 
  \<open>x \<in> S \<Longrightarrow> replicate n x setinterleaves ((replicate n x, replicate n x), S)\<close>
  by (induct n) auto

lemma replicate_strict_mono: \<open>strict_mono (\<lambda>i. replicate i x)\<close>
proof (rule strict_monoI)
  fix i j :: nat assume \<open>i < j\<close>
  hence \<open>replicate j x = replicate i x @ replicate (j - i) x\<close>
    by (simp add: replicate_add[symmetric])
  moreover from \<open>i < j\<close> have \<open>replicate i x \<noteq> replicate j x\<close>
    by (metis length_replicate less_irrefl_nat)
  ultimately show \<open>replicate i x < replicate j x\<close>
    by (auto simp: less_list_def less_eq_list_def prefix_def)
qed



(*
lemma T_write0I: \<open>s \<in> \<T> Proc \<Longrightarrow> ev a # s \<in> \<T> (a \<rightarrow> Proc)\<close> by (simp add: T_write0)

lemma T_writeI: \<open>s \<in> \<T> Proc \<Longrightarrow> ev (c a) # s \<in> \<T> (c\<^bold>!a \<rightarrow> Proc)\<close> by (simp add: T_write)
lemma T_readI: \<open>inj_on c A \<Longrightarrow> x \<in> A \<Longrightarrow> s \<in> \<T> (Qf x) \<Longrightarrow> ev (c x) # s \<in> \<T> (read c A Qf)\<close>
  by (auto simp: T_read inv_into_f_f)
lemma T_DetI1: \<open>s \<in> \<T> Proc1 \<Longrightarrow> s \<in> \<T> (Proc1 \<box> Proc2)\<close> by (simp add: T_Det)
lemma T_DetI2: \<open>s \<in> \<T> Proc2 \<Longrightarrow> s \<in> \<T> (Proc1 \<box> Proc2)\<close> by (simp add: T_Det)
lemma T_ThrowI1: \<open>t \<in> \<T> Proc \<Longrightarrow> set t \<inter> ev ` A = {} \<Longrightarrow> t \<in> \<T> (Proc \<Theta> a \<in> A. Qf a)\<close>
  by (simp add: T_Throw)
lemma T_ThrowI2: \<open>t1 @ [ev a] \<in> \<T> Proc \<Longrightarrow> set t1 \<inter> ev ` A = {} \<Longrightarrow> a \<in> A \<Longrightarrow> t2 \<in> \<T> (Qf a)
                  \<Longrightarrow> t1 @ ev a # t2 \<in> \<T> (Proc \<Theta> a \<in> A. Qf a)\<close>
  unfolding T_Throw by blast *)
lemma T_SyncI_right: \<open>u \<in> \<T> Proc2 \<Longrightarrow> \<forall>x\<in>set u. x \<notin> range tick \<union> ev ` S \<Longrightarrow> u \<in> \<T> (Proc1 \<lbrakk>S\<rbrakk> Proc2)\<close>
  by (rule T_SyncI[OF Nil_elem_T], assumption, rule emptyLeftSelf) blast
lemma T_SyncI_left: \<open>t \<in> \<T> Proc1 \<Longrightarrow> \<forall>x\<in>set t. x \<notin> range tick \<union> ev ` S \<Longrightarrow> t \<in> \<T> (Proc1 \<lbrakk>S\<rbrakk> Proc2)\<close>
  by (metis Sync_commute T_SyncI_right)


lemma T_GlobalDetI: \<open>x \<in> A \<Longrightarrow> s \<in> \<T> (Pf x) \<Longrightarrow> s \<in> \<T> (\<box>x \<in> A. Pf x)\<close>
  by (auto simp: T_GlobalDet')


locale Dali =
  fixes MaxNIds MaxKeys MaxcPtr MaxVal MaxTid MaxEpoch :: nat
  assumes MaxcPtr_ge_2 : \<open>2 \<le> MaxcPtr\<close>
    \<comment> \<open>at least three pointers (active, in-flight, committed)\<close>
begin

definition NodeID :: \<open>NodeIDType set\<close>
  where \<open>NodeID = N ` {0 .. MaxNIds}\<close>

definition Key :: \<open>KeyType set\<close>
  where \<open>Key = K ` {0 .. MaxKeys}\<close>

definition Val :: \<open>ValType set\<close>
  where \<open>Val = V ` {0 .. MaxVal}\<close>

definition Pointer :: \<open>Pointers set\<close>
  where \<open>Pointer = P ` {0 .. MaxcPtr}\<close>

definition ThreadIDs :: \<open>ThreadID set\<close>
  where \<open>ThreadIDs = Th ` {0 .. MaxTid}\<close>

definition BucketEpochs :: \<open>BucketEpochType set\<close>
  where \<open>BucketEpochs \<equiv> BE ` {0 .. MaxEpoch}\<close>

lemma NodeID_nonempty[simp]: \<open>NodeID \<noteq> {}\<close>
  and Null_notin_NodeID[simp]: \<open>Null \<notin> NodeID\<close>
  and finite_NodeID[simp]: \<open>finite NodeID\<close>
  and finite_Key[simp]: \<open>finite Key\<close>
  and finite_Val[simp]: \<open>finite Val\<close>
  and finite_Pointer[simp]: \<open>finite Pointer\<close>
  and finite_ThreadIDs[simp]: \<open>finite ThreadIDs\<close>
  and finite_BucketEpochs[simp]: \<open>finite BucketEpochs\<close>
  by (auto simp: NodeID_def Key_def Val_def Pointer_def ThreadIDs_def BucketEpochs_def)

lemma NodeID_iff: \<open>x \<in> NodeID \<longleftrightarrow> (\<exists>i \<le> MaxNIds. x = N i)\<close>
  and ThreadIDs_iff: \<open>t \<in> ThreadIDs \<longleftrightarrow> (\<exists>i \<le> MaxTid. t = Th i)\<close>
  by (auto simp: NodeID_def ThreadIDs_def)

text\<open>Epochs are counted cyclically modulo \<open>MaxEpoch + 1\<close>:\<close>

fun epochToInt :: \<open>BucketEpochType \<Rightarrow> int\<close> where
  \<open>epochToInt (BE n) = int n\<close>

fun prevEpoch :: \<open>BucketEpochType \<Rightarrow> BucketEpochType\<close> where
  \<open>prevEpoch (BE n) = BE ((n + MaxEpoch) mod Suc MaxEpoch)\<close>

fun nextEpoch :: \<open>BucketEpochType \<Rightarrow> BucketEpochType\<close> where
  \<open>nextEpoch (BE n) = BE (Suc n mod Suc MaxEpoch)\<close>

fun intToEpoch :: \<open>int \<Rightarrow> BucketEpochType\<close> where
  \<open>intToEpoch x = (if 0 \<le> x \<and> x \<le> int MaxEpoch then BE (nat x) else BE MaxEpoch)\<close>

text\<open>The first pointer that is neither the active nor the committed one:\<close>

definition freePointer :: \<open>Pointers \<Rightarrow> Pointers \<Rightarrow> Pointers\<close>
  where \<open>freePointer a c \<equiv> P (LEAST i. P i \<noteq> a \<and> P i \<noteq> c)\<close>


(* concrete.csp*)

Fixrec NodeHandler :: \<open>NodeIDType \<Rightarrow> KeyType \<Rightarrow> ValType \<Rightarrow> NodeIDType \<Rightarrow> bool \<Rightarrow> channels process\<close>
  and InitNode :: \<open>NodeIDType \<Rightarrow> channels process\<close>
  where NodeHandler_rec [simp del]: \<open>NodeHandler me k v nxt pers =
       (getKey\<^bold>!(me,k) \<rightarrow> NodeHandler me k v nxt pers)
   \<box>   (getVal\<^bold>!(me,v) \<rightarrow> NodeHandler me k v nxt pers)
   \<box>   (getNext\<^bold>!(me,nxt) \<rightarrow> NodeHandler me k v nxt pers)
   \<box>   (setNext\<^bold>?(m,n)\<^bold>|(m = me \<and> n \<in> NodeID) \<rightarrow> NodeHandler me k v n pers)
   \<box>   (persistNode\<^bold>!me \<rightarrow> NodeHandler me k v nxt True)
   \<box>   (crash \<rightarrow>(if pers
                 then NodeHandler me k v nxt pers
                 else InitNode me))\<close>
  | InitNode_rec [simp del]: \<open>InitNode me =
      (initNode\<^bold>?(n,k,v)\<^bold>|(n = me) \<rightarrow> NodeHandler me k v Null False)
    \<box> (crash \<rightarrow> InitNode me)\<close>


definition alphaNode :: \<open>NodeIDType \<Rightarrow> channels set\<close>
  where \<open>alphaNode me \<equiv>
   {x. \<exists>k v. x = initNode (me,k,v)}
 \<union> {x. \<exists>v. x = getVal (me,v)}
 \<union> {x. \<exists>k. x = getKey (me,k)}
 \<union> {x. \<exists>n. x = getNext (me,n)}
 \<union> {x. \<exists>n. x = setNext (me,n)}
 \<union> {noFreeNode}
 \<union> {persistNode me}
 \<union> {crash}\<close>

definition AllNodes :: \<open>channels process\<close>
  where \<open>AllNodes \<equiv> \<^bold>|\<^bold>|\<^bold>| n \<in># mset_set NodeID. InitNode n\<close>

definition nodeSyncSet :: \<open>channels set\<close>
  where \<open>nodeSyncSet \<equiv> {x. \<exists>n\<in>NodeID. \<exists>k v. x = initNode (n,k,v)}
    \<union> {x. \<exists>n\<in>NodeID. \<exists>k. x = getKey (n,k)}
    \<union> {x. \<exists>n\<in>NodeID. \<exists>v. x = getVal (n,v)}
    \<union> {x. \<exists>n\<in>NodeID. \<exists>nxt. x = getNext (n,nxt)}
    \<union> {x. \<exists>n\<in>NodeID. \<exists>nxt. x = setNext (n,nxt)}
    \<union> {x. \<exists>n\<in>NodeID. x = persistNode n}
    \<union> {noFreeNode}
    \<union> {crash}\<close>

definition nodeSyncSeti :: \<open>channels set\<close>
  where \<open>nodeSyncSeti \<equiv> {x. \<exists>n\<in>NodeID. \<exists>k v. x = initNode (n,k,v)}
    \<union> {x. \<exists>n\<in>NodeID. \<exists>k. x = getKey (n,k)}
    \<union> {x. \<exists>n\<in>NodeID. \<exists>v. x = getVal (n,v)}
    \<union> {x. \<exists>n\<in>NodeID. \<exists>nxt. x = getNext (n,nxt)}
    \<union> {x. \<exists>n\<in>NodeID. \<exists>nxt. x = setNext (n,nxt)}
    \<union> {x. \<exists>n\<in>NodeID. x = persistNode n}
    \<union> {noFreeNode}\<close>


Fixrec PointerHandler :: \<open>Pointers \<Rightarrow> NodeIDType \<Rightarrow> channels process\<close>
  where PointerHandler_rec [simp del]: \<open>PointerHandler me node = 
        (setPointerNode\<^bold>?(p,n)\<^bold>|(p = me) \<rightarrow> PointerHandler me n)
     \<box>  (getPointerNode\<^bold>!(me,node) \<rightarrow> PointerHandler me node)\<close>

definition Pointers :: \<open>channels process\<close>
  where \<open>Pointers \<equiv> \<^bold>|\<^bold>|\<^bold>| p \<in># mset_set Pointer. PointerHandler p Null\<close>

definition pointerSyncSet :: \<open>channels set\<close>
  where \<open>pointerSyncSet \<equiv> {x. \<exists>p n. x = setPointerNode (p,n)}
 \<union> {x. \<exists>p n. x = getPointerNode (p,n)}\<close>

definition maxEpoch :: BucketEpochType
  where \<open>maxEpoch \<equiv> BE MaxEpoch\<close>


Fixrec BucketVarHandler :: \<open>Pointers \<Rightarrow> Pointers \<Rightarrow> Pointers \<Rightarrow> BucketEpochType \<Rightarrow> channels process\<close>
  where BucketVarHandler_rec [simp del]: \<open>BucketVarHandler a f c ss = (getBucketEpoch\<^bold>!ss \<rightarrow> BucketVarHandler a f c ss)
     \<box>  (getActiveNode\<^bold>!a \<rightarrow> BucketVarHandler a f c ss)
     \<box>  (getFlightNode\<^bold>!f \<rightarrow> BucketVarHandler a f c ss)
     \<box>  (getCommittedNode\<^bold>!c \<rightarrow> BucketVarHandler a f c ss)
     \<box>  (setStat\<^bold>?(newA,newF,newC,newSS) \<rightarrow> BucketVarHandler newA newF newC newSS)\<close>


definition InitBucket :: \<open>channels process\<close>
  where \<open>InitBucket \<equiv> BucketVarHandler P0 Bot P2 BE0\<close>

definition alphaBucket :: \<open>channels set\<close>
  where \<open>alphaBucket \<equiv> {x. \<exists>p. x = getActiveNode p}
\<union> {x. \<exists>p. x = getFlightNode p}
\<union> {x. \<exists>p. x = getCommittedNode p}
\<union> {x. \<exists>e. x = getBucketEpoch e}
\<union> {x. \<exists>a f c e. x = setStat (a,f,c,e)}\<close>


definition alphaLock :: \<open>channels set\<close>
  where \<open>alphaLock \<equiv> {lock, unlock}\<close>


Fixrec BucketLockHandler :: \<open>channels process\<close>
  where BucketLockHandler_rec [simp del]: \<open>BucketLockHandler = (lock \<rightarrow> unlock \<rightarrow> BucketLockHandler)\<close>

Fixrec FailureListHandler :: \<open>BucketEpochType set \<Rightarrow> BucketEpochType set \<Rightarrow> channels process\<close>
  where FailureListHandler_rec [simp del]: \<open>FailureListHandler fs pfs = (addFailure\<^bold>?f
            \<rightarrow> FailureListHandler (insert f fs) pfs)
    \<box>  (persistFailureList \<rightarrow> FailureListHandler fs fs)
    \<box>  (ssFail\<^bold>?(f,b)\<^bold>|(b = (f \<in> pfs)) \<rightarrow> FailureListHandler fs pfs)
    \<box>  (crash \<rightarrow> FailureListHandler pfs pfs)\<close>


definition InitFailureList :: \<open>channels process\<close>
  where \<open>InitFailureList \<equiv> FailureListHandler {} {}\<close>


definition alphaFailureList :: \<open>channels set\<close>
  where \<open>alphaFailureList \<equiv>
      {x. \<exists>f. x = addFailure f}
    \<union> {persistFailureList}
    \<union> {x. \<exists>f b. x = ssFail (f,b)}\<close>


Fixrec GlobalEpochHandler :: \<open>BucketEpochType \<Rightarrow> BucketEpochType \<Rightarrow> bool \<Rightarrow> channels process\<close>
  where GlobalEpochHandler_rec [simp del]: \<open>GlobalEpochHandler e pe lt =
       ((if lt
        then (getGlobalEpoch\<^bold>?(t,v)\<^bold>|((v = pe)) \<rightarrow> GlobalEpochHandler e pe lt)
        else (getGlobalEpoch\<^bold>?(t,v)\<^bold>|((v = e)) \<rightarrow> GlobalEpochHandler e pe lt)))
   \<box>  (getGlobalEpochW\<^bold>!e \<rightarrow> GlobalEpochHandler e pe lt)
   \<box>  (incGlobalEpoch \<rightarrow>
          (if e = maxEpoch
           then Skip
           else GlobalEpochHandler (nextEpoch e) pe lt))
   \<box>  (persistGlobalEpoch \<rightarrow> GlobalEpochHandler e e lt)
   \<box>  (crash \<rightarrow> GlobalEpochHandler pe pe False)
   \<box>  (setEpochLock\<^bold>?l \<rightarrow> GlobalEpochHandler e pe l)\<close>

definition InitGlobalEpoch :: \<open>channels process\<close>
  where \<open>InitGlobalEpoch \<equiv> GlobalEpochHandler BE0 BE0 False\<close>

definition alphaGlobalEpoch :: \<open>channels set\<close>
  where \<open>alphaGlobalEpoch \<equiv>
      {x. \<exists>t e. x = getGlobalEpoch (t,e)}
    \<union> {x. \<exists>e. x = getGlobalEpochW e}
    \<union> {incGlobalEpoch}
    \<union> {persistGlobalEpoch}
    \<union> {x. \<exists>l. x = setEpochLock l}
    \<union> {crash}\<close>



Fixrec GlobalArrayHandler :: \<open>(ThreadID \<Rightarrow> BucketEpochType) \<Rightarrow> channels process\<close>
  where GlobalArrayHandler_rec [simp del]: \<open>GlobalArrayHandler tm =
       (getTIDTransaction\<^bold>?(t,e)\<^bold>|(t \<in> ThreadIDs \<and> e = tm t) \<rightarrow> GlobalArrayHandler tm)
   \<box>   (getGlobalEpoch\<^bold>?(t,e) \<rightarrow> GlobalArrayHandler (tm(t := e)))
   \<box>   (resRead\<^bold>?(t,v) \<rightarrow> GlobalArrayHandler (tm(t := BE0)))
   \<box>   (resUpdate\<^bold>?t \<rightarrow> GlobalArrayHandler (tm(t := BE0)))
   \<box>   (resUpdateFull\<^bold>?t \<rightarrow> GlobalArrayHandler (tm(t := BE0)))\<close>


definition initMap :: \<open>ThreadID \<Rightarrow> BucketEpochType\<close>
  where \<open>initMap \<equiv> (\<lambda>_. BE0)\<close>

definition InitGlobalArray :: \<open>channels process\<close>
  where \<open>InitGlobalArray \<equiv> GlobalArrayHandler initMap\<close>

definition transSyncSet :: \<open>channels set\<close>
  where \<open>transSyncSet \<equiv>
      {x. \<exists>t e. x = getTIDTransaction (t,e)}
    \<union> {x. \<exists>t e. x = getGlobalEpoch (t,e)}
    \<union> {x. \<exists>t v. x = resRead (t,v)}
    \<union> {x. \<exists>t. x = resUpdate t}
    \<union> {x. \<exists>t. x = resUpdateFull t}\<close>

definition alphaTransArray :: \<open>channels set\<close>
  where \<open>alphaTransArray \<equiv> {x. \<exists>t e. x = getTIDTransaction (t,e)}\<close>


Fixrec FreeTIDsHandler :: \<open>ThreadID set \<Rightarrow> channels process\<close>
  where FreeTIDsHandler_rec [simp del]: \<open>FreeTIDsHandler F =
       (pickFreeTID\<^bold>?t\<^bold>|(t \<in> F) \<rightarrow> FreeTIDsHandler (F - {t}))\<close>

definition FreeTIDs :: \<open>channels process\<close>
  where \<open>FreeTIDs \<equiv> FreeTIDsHandler ThreadIDs\<close>

definition SyncSetFreeTIDs :: \<open>channels set\<close>
  where \<open>SyncSetFreeTIDs \<equiv> {x. \<exists>t. x = pickFreeTID t}\<close>


section\<open> APPLICATION THREAD Methods \<close>

text\<open>The application thread loops: after a response, it continues as \<open>Thread\<close>
(as in \<open>concrete.csp\<close>); the thread methods form one system of mutually recursive processes.\<close>

Fixrec ReadSearch :: \<open>ThreadID \<Rightarrow> KeyType \<Rightarrow> NodeIDType \<Rightarrow> channels process\<close>
  and Read :: \<open>ThreadID \<Rightarrow> KeyType \<Rightarrow> channels process\<close>
  and SetStat :: \<open>ThreadID \<Rightarrow> BucketEpochType \<Rightarrow> Pointers \<Rightarrow> Pointers \<Rightarrow> Pointers \<Rightarrow> channels process\<close>
  and Lookup :: \<open>ThreadID \<Rightarrow> BucketEpochType \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> NodeIDType \<Rightarrow> Pointers \<Rightarrow> BucketEpochType \<Rightarrow> channels process\<close>
  and Update' :: \<open>ThreadID \<Rightarrow> NodeIDType \<Rightarrow> BucketEpochType \<Rightarrow> channels process\<close>
  and Update :: \<open>ThreadID \<Rightarrow> KeyType \<Rightarrow> ValType \<Rightarrow> channels process\<close>
  and Thread :: \<open>ThreadID \<Rightarrow> channels process\<close>
  where ReadSearch_rec [simp del]: \<open>ReadSearch me key validHead = 
        (if validHead = Null 
        then resRead\<^bold>!(me,TNull) \<rightarrow>  unlock \<rightarrow> Thread me
        else (getKey\<^bold>?(n,k)\<^bold>|(n = validHead \<and> k \<in> Key)
              \<rightarrow> (if key = k
                 then (getVal\<^bold>?(n,value)\<^bold>|(n = validHead) \<rightarrow> resRead\<^bold>!(me,value)
                       \<rightarrow> unlock \<rightarrow> Thread me)
                 else (getNext\<^bold>?(n,next)\<^bold>|(n = validHead)  \<rightarrow> ReadSearch me key next))))\<close>
  | Read_rec [simp del]: \<open>Read me key = lock
     \<rightarrow>  getGlobalEpoch\<^bold>?(t,e)\<^bold>|(t = me)  \<rightarrow>  getBucketEpoch\<^bold>?SS
     \<rightarrow>  (if SS = BE0 
         then ReadSearch me key Null
         else ssFail\<^bold>?(f,currFail)\<^bold>|(f = SS)
     \<rightarrow>  (if \<not> currFail 
         then (getActiveNode\<^bold>?headNode \<rightarrow> getPointerNode\<^bold>?(p,h)\<^bold>|(p = headNode)
               \<rightarrow> ReadSearch me key h)
         else ssFail\<^bold>?(f2,prevFail)\<^bold>|(f2 = prevEpoch SS) \<rightarrow> getFlightNode\<^bold>?headNodef
      \<rightarrow> (if ((\<not> prevFail) \<and> (headNodef \<noteq> Bot)) 
         then getPointerNode\<^bold>?(p,h)\<^bold>|(p = headNodef) \<rightarrow> ReadSearch me key h
         else getCommittedNode\<^bold>?headNodec \<rightarrow> getPointerNode\<^bold>?(p,h)\<^bold>|(p = headNodec)
              \<rightarrow> ReadSearch me key h)))\<close>
  | SetStat_rec [simp del]: \<open>SetStat me epoch newA newF newC = setStat\<^bold>!(newA,newF,newC,epoch)
     \<rightarrow>  resUpdate\<^bold>!me
     \<rightarrow>  unlock
     \<rightarrow>  Thread me\<close>
  | Lookup_rec [simp del]: \<open>Lookup me SS currFail prevFail newNode headNode epoch =
      getPointerNode\<^bold>?(p,h)\<^bold>|(p = headNode)
   \<rightarrow>  setNext\<^bold>!(newNode,h)
   \<rightarrow>  getActiveNode\<^bold>?oldA
   \<rightarrow>  getFlightNode\<^bold>?oldF
   \<rightarrow>  getCommittedNode\<^bold>?oldC
   \<rightarrow> (if SS = epoch 
      then setPointerNode\<^bold>!(oldA,newNode) \<rightarrow> SetStat me epoch oldA oldF oldC
      else if (SS = prevEpoch epoch \<and> (\<not> currFail) \<and> (\<not> prevFail) \<and> (oldF \<noteq> Bot)) 
      then setPointerNode\<^bold>!(oldC,newNode) \<rightarrow> SetStat me epoch oldC oldA oldF
      else if (SS = prevEpoch epoch \<and> (\<not> currFail) \<and> (oldF = Bot)) 
      then (setPointerNode\<^bold>!(freePointer oldA oldC,newNode)
            \<rightarrow> SetStat me epoch (freePointer oldA oldC) oldA oldC)
      else if (SS = prevEpoch epoch \<and> (\<not> currFail)) 
      then setPointerNode\<^bold>!(oldF,newNode) \<rightarrow> SetStat me epoch oldF oldA oldC
      else if (SS = prevEpoch epoch) 
      then setPointerNode\<^bold>!(oldA,newNode) \<rightarrow> SetStat me epoch oldA Bot oldC
      else if (epochToInt SS < epochToInt (prevEpoch epoch) \<and> (\<not> currFail)) 
      then setPointerNode\<^bold>!(oldC,newNode) \<rightarrow> SetStat me epoch oldC Bot oldA
      else if (epochToInt SS < epochToInt (prevEpoch epoch) \<and> currFail \<and> (\<not> prevFail) \<and> (oldF \<noteq> Bot)) 
      then setPointerNode\<^bold>!(oldA,newNode) \<rightarrow> SetStat me epoch oldA Bot oldF
      else setPointerNode\<^bold>!(oldA,newNode) \<rightarrow> SetStat me epoch oldA Bot oldC)\<close>
  | Update'_rec [simp del]: \<open>Update' me node gepoch = getBucketEpoch\<^bold>?SS \<rightarrow>
        (if SS = BE0 
        then getActiveNode\<^bold>?headNode \<rightarrow>  Lookup me SS False False node headNode gepoch
        else ssFail\<^bold>?(f,currFail)\<^bold>|(f = SS) \<rightarrow>  ssFail\<^bold>?(f2,prevFail)\<^bold>|(f2 = prevEpoch SS)
        \<rightarrow> (if \<not> currFail 
           then getActiveNode\<^bold>?headNode \<rightarrow>  Lookup me SS currFail prevFail node headNode gepoch
           else getFlightNode\<^bold>?headNodef
           \<rightarrow> (if ((\<not> prevFail) \<and> (headNodef \<noteq> Bot)) 
              then Lookup me SS currFail prevFail node headNodef gepoch
              else getCommittedNode\<^bold>?headNodec 
               \<rightarrow>  Lookup me SS currFail prevFail node headNodec gepoch)))\<close>
  | Update_rec [simp del]: \<open>Update me key val = lock \<rightarrow>  getGlobalEpoch\<^bold>?(t,e)\<^bold>|(t = me)
     \<rightarrow> ((initNode\<^bold>?(node,k,v)\<^bold>|(k = key \<and> v = val) \<rightarrow> Update' me node e)
       \<box> (noFreeNode \<rightarrow> resUpdateFull\<^bold>!me \<rightarrow> unlock \<rightarrow> Thread me))\<close>
  | Thread_rec [simp del]: \<open>Thread me =(invRead\<^bold>?(t,k)\<^bold>|(t = me) \<rightarrow> Read me k)
       \<box>  (invUpdate\<^bold>?(t,k,v)\<^bold>|(t = me) \<rightarrow> Update me k v)\<close>


section\<open> WORKER THREAD METHODS \<close>

Fixrec WaitOnTransactions :: \<open>ThreadID set \<Rightarrow> BucketEpochType \<Rightarrow> channels process\<close>
  where WaitOnTransactions_rec [simp del]: \<open>WaitOnTransactions Threads e =
      (if Threads = {}
       then Skip
       else getTIDTransaction\<^bold>?(t,v)\<^bold>|(t \<in> Threads) \<rightarrow>
                (if v \<noteq> e
                 then WaitOnTransactions (Threads - {t}) e
                 else WaitOnTransactions Threads e))\<close>

Fixrec WriteBackLoop :: \<open>NodeIDType \<Rightarrow> NodeIDType \<Rightarrow> channels process\<close>
  where WriteBackLoop_rec [simp del]: \<open>WriteBackLoop cnode n =
      (if n = Null
       then Skip
       else persistNode\<^bold>!n
         \<rightarrow> getNext\<^bold>?(x,n2)\<^bold>|(x = n)
         \<rightarrow> (if n2 = cnode
            then Skip
            else WriteBackLoop cnode n2))\<close>

Fixrec WriteBack :: \<open>channels process\<close>
  where WriteBack_rec [simp del]: \<open>WriteBack =
      getCommittedNode\<^bold>?cnode
   \<rightarrow>  getActiveNode\<^bold>?n
   \<rightarrow>  getPointerNode\<^bold>?(p1,c)\<^bold>|(p1 = cnode)
   \<rightarrow>  getPointerNode\<^bold>?(p2,a)\<^bold>|(p2 = n)
   \<rightarrow>  WriteBackLoop c a\<close>

Fixrec WorkerThread :: \<open>channels process\<close>
  where WorkerThread_rec [simp del]: \<open>WorkerThread =
      getGlobalEpochW\<^bold>?e
   \<rightarrow>  setEpochLock\<^bold>!True
   \<rightarrow>  incGlobalEpoch
   \<rightarrow>  persistGlobalEpoch
   \<rightarrow>  setEpochLock\<^bold>!False
   \<rightarrow> ((WaitOnTransactions ThreadIDs e)
        \<^bold>; WriteBack
        \<^bold>; WorkerThread)\<close>

definition ApplicationThreads :: \<open>channels process\<close>
  where \<open>ApplicationThreads \<equiv> (pickFreeTID\<^bold>?t1 \<rightarrow> Thread t1) ||| (pickFreeTID\<^bold>?t2 \<rightarrow> Thread t2)\<close>

definition AllThreads :: \<open>channels process\<close>
  where \<open>AllThreads \<equiv> ApplicationThreads ||| WorkerThread\<close>

definition Recovery :: \<open>channels process\<close>
  where \<open>Recovery \<equiv> getGlobalEpochW\<^bold>?F
   \<rightarrow>  addFailure\<^bold>!F
   \<rightarrow>  addFailure\<^bold>!(prevEpoch F)
   \<rightarrow>  persistFailureList
   \<rightarrow>  setEpochLock\<^bold>!True
   \<rightarrow>  incGlobalEpoch
   \<rightarrow>  persistGlobalEpoch
   \<rightarrow>  setEpochLock\<^bold>!False
   \<rightarrow>  Skip\<close>

definition alphaCrash :: \<open>channels set\<close>
  where \<open>alphaCrash \<equiv> {crash}\<close>


definition alphaGlobal :: \<open>channels set\<close>
  where \<open>alphaGlobal \<equiv> alphaFailureList \<union> alphaGlobalEpoch\<close>


definition alphaG :: \<open>channels set\<close>
  where \<open>alphaG \<equiv>  alphaGlobal
    \<union> nodeSyncSet
    \<union> alphaBucket
    \<union> SyncSetFreeTIDs
    \<union> alphaCrash
    \<union> pointerSyncSet\<close>

definition GlobalProcesses :: \<open>channels process\<close>
  where \<open>GlobalProcesses \<equiv> (((AllNodes \<lbrakk>alphaCrash\<rbrakk> InitGlobalEpoch)
        \<lbrakk>alphaCrash\<rbrakk>
        InitFailureList)
      ||| InitBucket
      ||| FreeTIDs
      ||| Pointers)\<close>

definition DaliArray :: \<open>channels process\<close>
  where \<open>DaliArray \<equiv> ((AllThreads \<lbrakk>transSyncSet\<rbrakk> InitGlobalArray)
       \ alphaTransArray)\<close>

definition DaliMethods :: \<open>channels process\<close>
  where \<open>DaliMethods \<equiv> ((DaliArray \<lbrakk>alphaLock\<rbrakk> BucketLockHandler)
       \ alphaLock)\<close>

definition internalEvents :: \<open>channels set\<close>
  where \<open>internalEvents \<equiv> alphaGlobal
    \<union> nodeSyncSeti
    \<union> alphaBucket
    \<union> SyncSetFreeTIDs
    \<union> pointerSyncSet\<close>

definition DaliL :: \<open>channels process\<close>
  where \<open>DaliL \<equiv> ((DaliMethods \<lbrakk>alphaG\<rbrakk> GlobalProcesses) \ internalEvents)\<close>

definition DaliRecovery :: \<open>channels process\<close>
  where \<open>DaliRecovery \<equiv> Recovery \<^bold>; DaliMethods\<close>

Fixrec DaliCrash :: \<open>channels process\<close>
  and DaliCrashR :: \<open>channels process\<close>
  where DaliCrash_rec [simp del]: \<open>DaliCrash =
       ((DaliMethods ||| (crash \<rightarrow> Skip))
          \<Theta> a \<in> alphaCrash. DaliCrashR)\<close>
 | DaliCrashR_rec [simp del]:
   \<open>DaliCrashR =
       ((DaliRecovery ||| (crash \<rightarrow> Skip))
          \<Theta> a \<in> alphaCrash. DaliCrashR)\<close>

definition Dali :: \<open>channels process\<close>
  where \<open>Dali \<equiv> ((DaliCrash \<lbrakk>alphaG\<rbrakk> GlobalProcesses) \ internalEvents)\<close>

definition DaliE :: \<open>channels process\<close>
  where \<open>DaliE \<equiv> Dali \ {x. \<exists>t k. x = invRead (t,k)} \ {x. \<exists>t k v. x = invUpdate (t,k,v)}\<close>

(* spec.csp*)

section\<open>ABSTRACT MAP SPECIFICATION\<close>

definition maxNodes :: int
  where \<open>maxNodes \<equiv> int (card NodeID)\<close>


type_synonym MapMem = \<open>KeyType \<Rightarrow> ValType\<close>

type_synonym MapState = \<open>MapMem \<times> MapMem \<times> int \<times> int\<close>

definition emptyMap :: MapMem
  where \<open>emptyMap \<equiv> (\<lambda>_. TNull)\<close>

definition mapLookupNull :: \<open>MapMem \<Rightarrow> KeyType \<Rightarrow> ValType\<close>
  where \<open>mapLookupNull m k \<equiv> m k\<close>

definition mapUpdate :: \<open>MapMem \<Rightarrow> KeyType \<Rightarrow> ValType \<Rightarrow> MapMem\<close>
  where \<open>mapUpdate m k v \<equiv> m(k := v)\<close>


(*vmem = volatile memory
  pmem = persisted memory
  c    = nodes that may have been used
  pc   = persisted node count

  crash -> nondeterministically rollback to any x in {pc..c}
*)

Fixrec MapOps :: \<open>MapState \<Rightarrow> channels process\<close>
  where MapOps_rec [simp del]: \<open>MapOps (vmem, pmem, c, pmemc) = 
        ((if vmem = emptyMap
          then (doRead\<^bold>?(t,k,v)\<^bold>|(v = TNull) \<rightarrow> MapOps (vmem, pmem, c, pmemc))
          else (doRead\<^bold>?(t,k,v)\<^bold>|(v = mapLookupNull vmem k) \<rightarrow> MapOps (vmem, pmem, c, pmemc))))
    \<box>  ((if c < maxNodes 
         then (doUpdate\<^bold>?(t,k,v) \<rightarrow> MapOps (mapUpdate vmem k v, pmem, c + 1, pmemc))
         else (doUpdateFull\<^bold>?t \<rightarrow> MapOps (vmem, pmem, c, pmemc))))
    \<box>  (crash \<rightarrow> (\<box>x \<in> {pmemc..c}. MapOps (pmem, pmem, x, x)))
    \<box>  (persist \<rightarrow> MapOps (vmem, vmem, c, c))\<close>

definition MapSpec0 :: \<open>channels process\<close>
  where \<open>MapSpec0 \<equiv> MapOps (emptyMap, emptyMap, 0, 0)\<close>

definition MapSpec :: \<open>channels process\<close>
  where \<open>MapSpec \<equiv> MapSpec0\<close>

Fixrec Persist :: \<open>channels process\<close>
  where Persist_rec : \<open>Persist = persist \<rightarrow> Persist\<close>

Fixrec AllThreadHandler :: \<open>ThreadID set \<Rightarrow> channels process\<close>
  where AllThreadHandler_rec : \<open>AllThreadHandler usedThreads =
                                   (invRead\<^bold>?(t,k) \<rightarrow> AllThreadHandler (insert t usedThreads))
                                \<box>  (invUpdate\<^bold>?(t,k,v) \<rightarrow> AllThreadHandler (insert t usedThreads))
                                \<box>  (getUsedThreads\<^bold>!usedThreads \<rightarrow> AllThreadHandler usedThreads)\<close>

Fixrec MapThread :: \<open>ThreadID \<Rightarrow> channels process\<close>
  where MapThread_rec : \<open>MapThread me =   (invRead\<^bold>?(t,key)\<^bold>|(t = me)
                                            \<rightarrow> doRead\<^bold>?(t2,k2,value)\<^bold>|(t2 = me \<and> k2 = key)
                                               \<rightarrow> resRead\<^bold>!(me,value) \<rightarrow> MapThread me)
                                       \<box> (invUpdate\<^bold>?(t,key,value)\<^bold>|(t = me)
                                            \<rightarrow> ((doUpdateFull\<^bold>!me
                                                  \<rightarrow> resUpdateFull\<^bold>!me \<rightarrow> MapThread me)
                                                \<box> (doUpdate\<^bold>!(me,key,value)
                                                      \<rightarrow> resUpdate\<^bold>!me
                                                           \<rightarrow> MapThread me)))\<close>

Fixrec AllMapThreads :: \<open>channels process\<close>
  where AllMapThreads_rec : \<open>AllMapThreads = getUsedThreads\<^bold>?ts
                                             \<rightarrow> (\<^bold>|\<^bold>|\<^bold>| t \<in># mset_set (ThreadIDs - ts). MapThread t)\<close>

definition specSyncSet :: \<open>channels set\<close>
  where \<open>specSyncSet   \<equiv> {x. \<exists>t k v. x = doUpdate (t,k,v)}
                       \<union> {x. \<exists>t k v. x = doRead (t,k,v)}
                       \<union> {x. \<exists>t. x = doUpdateFull t}
                       \<union> {crash}
                       \<union> {persist}\<close>

definition internal   :: \<open>channels set\<close>
  where \<open>internal      \<equiv> {x. \<exists>t k v. x = doUpdate (t,k,v)}
                       \<union> {x. \<exists>t k v. x = doRead (t,k,v)}
                       \<union> {x. \<exists>t. x = doUpdateFull t}
                       \<union> {persist}\<close>

definition threadSyncSet :: \<open>channels set\<close>
  where \<open>threadSyncSet \<equiv> {x. \<exists>t k. x = invRead (t,k)}
                       \<union> {x. \<exists>t k v. x = invUpdate (t,k,v)}
                       \<union> {x. \<exists>ts. x = getUsedThreads ts}\<close>

definition internalSpec :: \<open>channels set\<close>
  where \<open>internalSpec \<equiv> {x. \<exists>t k v. x = doUpdate (t,k,v)}
                      \<union> {x. \<exists>t k v. x = doRead (t,k,v)}
                      \<union> {x. \<exists>t. x = doUpdateFull t}
                      \<union> {persist}\<close>

definition alphaThread :: \<open>channels set\<close>
  where \<open>alphaThread \<equiv> {x. \<exists>ts. x = getUsedThreads ts}\<close>

definition SpecThreadsL :: \<open>channels process\<close>
  where \<open>SpecThreadsL \<equiv> ((AllMapThreads \<lbrakk>threadSyncSet\<rbrakk> AllThreadHandler {}) \ alphaThread)\<close>

definition SpecL :: \<open>channels process\<close>
  where \<open>SpecL \<equiv> ((SpecThreadsL \<lbrakk>specSyncSet\<rbrakk> MapSpec) \ internalSpec)\<close>


Fixrec Spec_with_crash :: \<open>channels process\<close>
  where Spec_with_crash_rec : \<open>Spec_with_crash = ((AllMapThreads ||| (crash \<rightarrow> Skip))
                                                 \<Theta> a \<in> {crash}. Spec_with_crash)\<close>

definition SpecThreads :: \<open>channels process\<close>
  where \<open>SpecThreads \<equiv> (((Spec_with_crash \<lbrakk>threadSyncSet\<rbrakk> AllThreadHandler {}) \ alphaThread)
                       ||| Persist)\<close>

definition Spec :: \<open>channels process\<close>
  where \<open>Spec \<equiv> ((SpecThreads \<lbrakk>specSyncSet\<rbrakk> MapSpec) \ internalSpec)\<close>
text\<open>Note that the event \<^term>\<open>persist\<close> is in \<^term>\<open>internalSpec\<close>, and since
 \<^term>\<open>Persist = persist \<rightarrow> Persist\<close> can happen at any time, the hiding operator will
thus produce a \<^term>\<open>\<bottom>\<close> for this trace. Thus, there is a divergence in this model 
(which was already present in the original version by Edmonds, Derrick, et al). 
This limits the current model to trace - and failure analysis. An alternative would 
have been to exclude \<^term>\<open>persist\<close> from the internals, but this has other consequences.\<close>


text\<open>Formally: an infinite run of hidden \<^const>\<open>persist\<close> events makes \<^const>\<open>Spec\<close> divergent
from the start, i.e., equal to \<open>\<bottom>\<close>:\<close>

lemma persist_Persist: \<open>replicate n (ev persist) \<in> \<T> Persist\<close>
  by (induct n) (simp, subst Persist_rec, simp add: T_write0)

lemma persist_MapOps: \<open>replicate n (ev persist) \<in> \<T> (MapOps (m, m, c, c))\<close>
proof (induct n arbitrary: m c)
  case 0 show ?case by simp
next
  case (Suc n) show ?case
    by (subst MapOps_rec, unfold T_Det, rule UnI2) (simp add: T_write0 Suc)
qed

lemma persist_SpecThreads: \<open>replicate n (ev persist) \<in> \<T> SpecThreads\<close>
  unfolding SpecThreads_def 
  by (rule T_SyncI[OF Nil_elem_T persist_Persist], rule emptyLeftSelf) auto

lemma persist_SpecU: \<open>replicate n (ev persist) \<in> \<T> (SpecThreads \<lbrakk>specSyncSet\<rbrakk> MapSpec)\<close>
proof (unfold MapSpec_def MapSpec0_def, rule T_SyncI)
  show \<open>replicate n (ev persist) \<in> \<T> SpecThreads\<close> by (fact persist_SpecThreads)
  show \<open>replicate n (ev persist) \<in> \<T> (MapOps (emptyMap, emptyMap, 0, 0))\<close> by (fact persist_MapOps)
  show \<open>replicate n (ev persist) setinterleaves 
          ((replicate n (ev persist), replicate n (ev persist)), range tick \<union> ev ` specSyncSet)\<close>
    by (rule replicate_setinterleaves) (simp add: specSyncSet_def)
qed

lemma Spec_is_BOT: \<open>Spec = \<bottom>\<close>
proof -
  let ?f = \<open>\<lambda>i. replicate i (ev persist)\<close>
  have run : \<open>isInfHiddenRun ?f (SpecThreads \<lbrakk>specSyncSet\<rbrakk> MapSpec) internalSpec\<close>
    by (simp add: replicate_strict_mono persist_SpecU internalSpec_def)
  have start : \<open>[] \<in> range ?f\<close> by (metis range_eqI replicate_0)
  have hide : \<open>[] = trace_hide [] (ev ` internalSpec) @ []\<close> by simp
  have \<open>[] \<in> \<D> Spec\<close>
    unfolding Spec_def D_Hiding mem_Collect_eq
    using run start hide ftF_Nil tF_Nil by blast
  thus \<open>Spec = \<bottom>\<close> by (simp add: BOT_iff_Nil_D)
qed

definition alphaEndEvents :: \<open>channels set\<close>
  where \<open>alphaEndEvents \<equiv>    {x. \<exists>t v. x = resRead (t,v)}
                           \<union> {x. \<exists>t. x = resUpdate t}
                           \<union> {x. \<exists>t. x = resUpdateFull t}\<close>


definition SpecE :: \<open>channels process\<close>
  where \<open>SpecE \<equiv> Spec \ alphaEndEvents\<close>


end (* locale Dali *)

section\<open>The General Dali Model Instantiated\<close>

text\<open>The original, finite model of the article is the instance with three nodes and pointers,
two keys, values and threads, and three epochs:\<close>

locale Dali_orig = Dali 2 1 2 1 1 2
  \<comment> \<open>the instance as a context for tests: inside, \<open>Spec\<close>, \<open>Dali\<close>, \<open>NodeID\<close>, ... 
     denote the processes and data of this instance\<close>

text\<open>The instance is consistent:\<close>
interpretation orig : Dali_orig by standard simp

context Dali_orig begin

lemma \<open>NodeID = {N0, N1, N2}\<close> and \<open>ThreadIDs = {T0, T1}\<close>
  unfolding set_eq_iff NodeID_iff ThreadIDs_iff
  by (auto simp: numeral_2_eq_2 le_Suc_eq)


subsection \<open>Component Traces\<close>

lemma ThreadIDs_orig: \<open>ThreadIDs = {T0, T1}\<close>
  unfolding set_eq_iff ThreadIDs_iff by (auto simp: le_Suc_eq)

lemma NodeID_orig: \<open>NodeID = {N0, N1, N2}\<close>
  unfolding set_eq_iff NodeID_iff by (auto simp: numeral_2_eq_2 le_Suc_eq)

lemma maxNodes_orig: \<open>maxNodes = 3\<close> by (simp add: maxNodes_def NodeID_orig)

lemma MapThread_update_trace:
  \<open>[ev (invUpdate (T0,K0,V0)), ev (doUpdate (T0,K0,V0)), ev (resUpdate T0)] \<in> \<T> (MapThread T0)\<close>
  apply (subst MapThread_rec, rule T_DetI2, rule T_readI[where x = \<open>(T0,K0,V0)\<close>])
    apply (simp_all add: inj_on_def)
  by (rule T_DetI2, rule T_writeI, rule T_writeI, rule Nil_elem_T)

lemma MapThread_read_trace:
  \<open>[ev (invRead (T1,K0)), ev (doRead (T1,K0,V0)), ev (resRead (T1,V0))] \<in> \<T> (MapThread T1)\<close>
  apply (subst MapThread_rec, rule T_DetI1, rule T_readI[where x = \<open>(T1,K0)\<close>])
    apply (simp_all add: inj_on_def)
  apply (rule T_readI)
    apply (simp_all add: inj_on_def)
  by (rule T_writeI, rule Nil_elem_T)

lemma AllMapThreads_trace1:
  \<open>[ev (getUsedThreads {}), 
    ev (invUpdate (T0,K0,V0)), 
    ev (doUpdate (T0,K0,V0)), 
    ev (resUpdate T0)]
   \<in> \<T> AllMapThreads\<close>
  apply (subst AllMapThreads_rec, rule T_readI[where x = \<open>{}\<close>])
    apply (simp_all add: inj_on_def ThreadIDs_orig[simplified])
  by (rule T_SyncI_left[OF MapThread_update_trace]) auto

lemma AllMapThreads_trace2:
  \<open>[ev (getUsedThreads {T0}), 
    ev (invRead (T1,K0)), 
    ev (doRead (T1,K0,V0)), 
    ev (resRead (T1,V0))]
   \<in> \<T> AllMapThreads\<close>
  apply (subst AllMapThreads_rec, rule T_readI[where x = \<open>{T0}\<close>])
    apply (simp_all add: inj_on_def ThreadIDs_orig[simplified] insert_Diff_if)
  using MapThread_read_trace by simp

lemma Spec_with_crash_trace:
  \<open>[ev (getUsedThreads {}), ev (invUpdate (T0,K0,V0)), ev (doUpdate (T0,K0,V0)), ev (resUpdate T0)]
   @ ev crash #
   [ev (getUsedThreads {T0}), ev (invRead (T1,K0)), ev (doRead (T1,K0,V0)), ev (resRead (T1,V0))]
   \<in> \<T> Spec_with_crash\<close>
proof (subst Spec_with_crash_rec, rule T_ThrowI2)
  show \<open>[ev (getUsedThreads {}), ev (invUpdate (T0,K0,V0)), ev (doUpdate (T0,K0,V0)), ev (resUpdate T0)]
        @ [ev crash] \<in> \<T> (AllMapThreads ||| (crash \<rightarrow> Skip))\<close>
    by (rule T_SyncI[OF AllMapThreads_trace1 T_write0I[OF Nil_elem_T]]) auto
  show \<open>[ev (getUsedThreads {T0}), ev (invRead (T1,K0)), ev (doRead (T1,K0,V0)), ev (resRead (T1,V0))]
        \<in> \<T> Spec_with_crash\<close>
    by (subst Spec_with_crash_rec, rule T_ThrowI1, rule T_SyncI_left[OF AllMapThreads_trace2]) auto
qed auto

lemma AllThreadHandler_trace:
  \<open>[ev (getUsedThreads {}), 
    ev (invUpdate (T0,K0,V0)), 
    ev (getUsedThreads {T0}), 
    ev (invRead (T1,K0))]
   \<in> \<T> (AllThreadHandler {})\<close>
  apply (subst AllThreadHandler_rec, rule T_DetI2, rule T_writeI)
  apply (subst AllThreadHandler_rec, rule T_DetI1, rule T_DetI2)
  apply (rule T_readI, simp add: inj_on_def, simp, simp only: prod.case)
  apply (subst AllThreadHandler_rec, rule T_DetI2, rule T_writeI)
  apply (subst AllThreadHandler_rec, rule T_DetI1, rule T_DetI1)
  by (rule T_readI, simp add: inj_on_def, simp, rule Nil_elem_T)

lemma MapSpec_trace:
  \<open>[ev (doUpdate (T0,K0,V0)), ev persist, ev crash, ev (doRead (T1,K0,V0))] \<in> \<T> MapSpec\<close>
proof -
  have c0: \<open>(0::int) < maxNodes\<close> by (simp add: maxNodes_orig)
  have m1: \<open>mapUpdate emptyMap K0 V0 \<noteq> emptyMap\<close>
    by (auto simp: mapUpdate_def emptyMap_def fun_eq_iff)
  show ?thesis
    unfolding MapSpec_def MapSpec0_def
    apply (subst MapOps_rec, rule T_DetI1, rule T_DetI1, rule T_DetI2)
    apply (simp only: if_P[OF c0])
    apply (rule T_readI, simp add: inj_on_def, simp, simp only: prod.case)
    apply (subst MapOps_rec, rule T_DetI2, rule T_write0I)
    apply (subst MapOps_rec, rule T_DetI1, rule T_DetI2, rule T_write0I)
    apply (rule T_GlobalDetI[where x = \<open>0 + 1\<close>], simp)
    apply (subst MapOps_rec, rule T_DetI1, rule T_DetI1, rule T_DetI1)
    apply (simp only: if_not_P[OF m1])
    by (rule T_readI, simp add: inj_on_def, 
        simp add: mapLookupNull_def mapUpdate_def, rule Nil_elem_T)
qed

lemma crash_Spec_with_crash: \<open>[ev crash] \<in> \<T> Spec_with_crash\<close>
proof -
  have \<open>[] @ ev crash # [] \<in> \<T> Spec_with_crash\<close>
  proof (subst Spec_with_crash_rec, rule T_ThrowI2)
    show \<open>[] @ [ev crash] \<in> \<T> (AllMapThreads ||| (crash \<rightarrow> Skip))\<close>
      by (simp, rule T_SyncI_right, rule T_write0I, rule Nil_elem_T, auto)
  qed simp_all
  thus ?thesis by simp
qed


section\<open>Assertions\<close> 

text\<open> Following \<open>assertions.csp\<close> in the original text.\<close>

lemma dali_trace_refinement: \<open>Spec \<sqsubseteq>\<^sub>T Dali\<close> oops

lemma daliL_trace_refinement: \<open>SpecL \<sqsubseteq>\<^sub>T DaliL\<close> oops

definition traces_hiding :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<Rightarrow> 'a set \<Rightarrow> ('a, 'r) trace\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k set\<close>
  where \<open>traces_hiding Proc A \<equiv> {trace_hide t (ev ` A) |t. t \<in> \<T> Proc}\<close>

lemma traces_hidingI: \<open>t \<in> \<T> Proc \<Longrightarrow> s = trace_hide t (ev ` A) \<Longrightarrow> s \<in> traces_hiding Proc A\<close>
  unfolding traces_hiding_def by blast

lemma spec_has_crash_trace:
  \<open>[ev crash] \<in> traces_hiding (SpecThreads \<lbrakk>specSyncSet\<rbrakk> MapSpec) internalSpec\<close>
proof (rule traces_hidingI)
  have \<open>[ev crash] \<in> \<T> SpecThreads\<close>
  proof (unfold SpecThreads_def, rule T_SyncI_left)
    have inner: \<open>[ev crash] \<in> \<T> (Spec_with_crash \<lbrakk>threadSyncSet\<rbrakk> AllThreadHandler {})\<close>
      by (rule T_SyncI_left[OF crash_Spec_with_crash]) (auto simp: threadSyncSet_def)
    have \<open>trace_hide [ev crash] (ev ` alphaThread) = [ev crash]\<close> by (auto simp: alphaThread_def)
    with mem_T_imp_mem_T_Hiding[OF inner, of alphaThread]
    show \<open>[ev crash] \<in> \<T> ((Spec_with_crash \<lbrakk>threadSyncSet\<rbrakk> AllThreadHandler {}) \ alphaThread)\<close>
      by metis
  qed auto
  moreover have \<open>[ev crash] \<in> \<T> MapSpec\<close>
    unfolding MapSpec_def MapSpec0_def
    by (subst MapOps_rec, rule T_DetI1, rule T_DetI2, rule T_write0I, rule Nil_elem_T)
  ultimately show \<open>[ev crash] \<in> \<T> (SpecThreads \<lbrakk>specSyncSet\<rbrakk> MapSpec)\<close>
    by (rule T_SyncI) (simp add: specSyncSet_def)
qed (auto simp: internalSpec_def)

lemma spec_trace_crash_read_value:
  \<open>map ev [invUpdate (T0,K0,V0), resUpdate T0, crash, invRead (T1,K0), resRead (T1,V0)]
   \<in> traces_hiding (SpecThreads \<lbrakk>specSyncSet\<rbrakk> MapSpec) internalSpec\<close>
proof (rule traces_hidingI)
  let ?tIn = \<open>[ev (getUsedThreads {}), ev (invUpdate (T0,K0,V0)), ev (doUpdate (T0,K0,V0)),
               ev (resUpdate T0), ev crash, ev (getUsedThreads {T0}), ev (invRead (T1,K0)),
               ev (doRead (T1,K0,V0)), ev (resRead (T1,V0))]\<close>
  let ?tX = \<open>[ev (invUpdate (T0,K0,V0)), ev (doUpdate (T0,K0,V0)), ev (resUpdate T0), ev crash,
              ev (invRead (T1,K0)), ev (doRead (T1,K0,V0)), ev (resRead (T1,V0))]\<close>
  let ?tST = \<open>[ev (invUpdate (T0,K0,V0)), ev (doUpdate (T0,K0,V0)), ev (resUpdate T0), ev persist,
               ev crash, ev (invRead (T1,K0)), ev (doRead (T1,K0,V0)), ev (resRead (T1,V0))]\<close>
  have inner: \<open>?tIn \<in> \<T> (Spec_with_crash \<lbrakk>threadSyncSet\<rbrakk> AllThreadHandler {})\<close>
    by (rule T_SyncI[OF Spec_with_crash_trace AllThreadHandler_trace]) (auto simp: threadSyncSet_def)
  have hide: \<open>trace_hide ?tIn (ev ` alphaThread) = ?tX\<close> by (auto simp: alphaThread_def)
  have X: \<open>?tX \<in> \<T> ((Spec_with_crash \<lbrakk>threadSyncSet\<rbrakk> AllThreadHandler {}) \ alphaThread)\<close>
    using mem_T_imp_mem_T_Hiding[OF inner, of alphaThread] hide by metis
  have persist: \<open>[ev persist] \<in> \<T> Persist\<close>
    by (subst Persist_rec, rule T_write0I, rule Nil_elem_T)
  have ST: \<open>?tST \<in> \<T> SpecThreads\<close>
    unfolding SpecThreads_def by (rule T_SyncI[OF X persist]) auto
  show \<open>?tST \<in> \<T> (SpecThreads \<lbrakk>specSyncSet\<rbrakk> MapSpec)\<close>
    by (rule T_SyncI[OF ST MapSpec_trace]) (auto simp: specSyncSet_def)
  show \<open>map ev [invUpdate (T0,K0,V0), resUpdate T0, crash, invRead (T1,K0), resRead (T1,V0)]
        = trace_hide ?tST (ev ` internalSpec)\<close>
    by (auto simp: internalSpec_def)
qed

lemma spec_trace_crash_read_null:
  \<open>map(ev)[
      invUpdate (T0,K0,V0),
      resUpdate T0,
      crash,
      invRead (T1,K0),
      resRead (T1,TNull)
   ] \<in> Traces Spec\<close>
  oops

lemma dali_has_crash_trace: \<open>[ev crash] \<in> Traces Dali\<close> oops

lemma dali_simple_update_trace: \<open>map(ev)[invUpdate (T0,K0,V0), resUpdate T0] \<in> Traces Dali\<close> oops

lemma dali_trace_crash_read_null:
  \<open>map(ev) [
      invUpdate (T0,K0,V0),
      resUpdate T0,
      crash,
      invRead (T1,K0),
      resRead (T1,TNull)
   ] \<in> Traces Dali\<close>
  oops

lemma dali_trace_crash_read_value:
  \<open>map(ev) [
      invUpdate (T0,K0,V0),
      resUpdate T0,
      crash,
      invRead (T1,K0),
      resRead (T1,V0)
   ] \<in> Traces Dali\<close>
  oops

lemma spec_trace_complex_1:
  \<open>map(ev) [
      invUpdate (T0,K0,V0),
      crash,
      invUpdate (T1,K1,V0),
      resUpdate T1,
      invUpdate (T1,K1,V1),
      resUpdate T1,
      invRead (T1,K1),
      resRead (T1,V1),
      invRead (T1,K0),
      resRead (T1,TNull)
   ] \<in> Traces Spec\<close>
  oops

lemma spec_trace_complex_2:
  \<open>map(ev) [
      invUpdate (T0,K0,V0),
      resUpdate T0,
      crash,
      invUpdate (T1,K1,V0),
      resUpdate T1,
      invUpdate (T1,K1,V1),
      resUpdate T1,
      invRead (T1,K1),
      resRead (T1,V1),
      invRead (T1,K0),
      resRead (T1,V0)
   ] \<in> Traces Spec\<close>
  oops

lemma dali_trace_complex_1:
  \<open>map(ev) [
      invUpdate (T0,K0,V0),
      crash,
      invUpdate (T1,K1,V0),
      resUpdate T1,
      invUpdate (T1,K1,V1),
      resUpdate T1,
      invRead (T1,K1),
      resRead (T1,V1),
      invRead (T1,K0),
      resRead (T1,TNull)
   ] \<in> Traces Dali\<close>
  oops


lemma dali_trace_complex_2:
  \<open>map(ev) [
      invUpdate (T0,K0,V0),
      resUpdate T0,
      crash,
      invUpdate (T1,K1,V0),
      resUpdate T1,
      invUpdate (T1,K1,V1),
      resUpdate T1,
      invRead (T1,K1),
      resRead (T1,V1),
      invRead (T1,K0),
      resRead (T1,V0)
   ] \<in> Traces Dali\<close>
  oops


lemma spec_trace_multi_crash_1:
  \<open>map(ev) [
      invUpdate (T0,K0,V0),
      crash,
      invUpdate (T1,K1,V0),
      resUpdate T1,
      crash,
      invUpdate (T2,K1,V1),
      resUpdate T2,
      invRead (T2,K1),
      resRead (T2,V1),
      invRead (T2,K0),
      resRead (T2,TNull)
   ] \<in> Traces Spec\<close>
  oops


lemma spec_trace_multi_crash_2:
  \<open>map(ev) [
      invUpdate (T0,K0,V0),
      resUpdate T0,
      crash,
      invUpdate (T1,K1,V0),
      resUpdate T1,
      invUpdate (T1,K1,V1),
      crash,
      invRead (T2,K1),
      resRead (T2,V0),
      invRead (T2,K0),
      resRead (T2,V0)
   ] \<in> Traces Spec\<close>
  oops


lemma dali_trace_complex_1:
  \<open>map(ev) [
      invUpdate (T0,K0,V0),
      crash,
      invUpdate (T1,K1,V0),
      resUpdate T1,
      invUpdate (T1,K1,V1),
      resUpdate T1,
      invRead (T1,K1),
      resRead (T1,V1),
      invRead (T1,K0),
      resRead (T1,TNull)
   ] \<in> Traces Dali\<close>
  oops


lemma dali_trace_multi_crash_epoch:
  \<open>map(ev) [
      invUpdate (T0,K0,V0),
      resUpdate T0,
      crash,
      invUpdate (T1,K1,V0),
      resUpdate T1,
      invUpdate (T1,K1,V1),
      crash,
      invRead (T2,K1),
      resRead (T2,V0),
      invRead (T2,K0),
      resRead (T2,V0)
   ] \<in> Traces Dali\<close>
  oops


lemma spec_trace_multi_crash_3:
  \<open>map(ev)[
      invUpdate (T0,K0,V0),
      resUpdate T0,
      crash,
      crash,
      invRead (T1,K0),
      resRead (T1,TNull),
      invUpdate (T1,K1,V0),
      resUpdate T1,
      invUpdate (T1,K0,V0),
      resUpdate T1,
      crash,
      invRead (T2,K1),
      resRead (T2,V0),
      invRead (T2,K0),
      resRead (T2,TNull)
   ] \<in> Traces Spec\<close>
  oops


lemma dali_trace_multi_crash_3:
  \<open>map(ev) [
      invUpdate (T0,K0,V0),
      resUpdate T0,
      crash,
      crash,
      invRead (T1,K0),
      resRead (T1,TNull),
      invUpdate (T1,K1,V0),
      resUpdate T1,
      invUpdate (T1,K0,V0),
      resUpdate T1,
      crash,
      invRead (T2,K1),
      resRead (T2,V0),
      invRead (T2,K0),
      resRead (T2,TNull)
   ] \<in> Traces Dali\<close>
  oops


lemma spec_trace_concurrent_1:
  \<open>map(ev) [
      invUpdate (T0,K0,V0),
      invUpdate (T1,K1,V1),
      resUpdate T0,
      resUpdate T1,
      crash,
      invRead (T2,K1),
      resRead (T2,V1),
      invRead (T2,K0),
      resRead (T2,V0)
   ] \<in> Traces Spec\<close>
  oops


lemma spec_trace_concurrent_2:
  \<open>map(ev) [
      invUpdate (T0,K0,V0),
      invUpdate (T1,K1,V1),
      resUpdate T0,
      resUpdate T1,
      crash,
      invRead (T2,K1),
      resRead (T2,TNull),
      invRead (T2,K0),
      resRead (T2,V0)
   ] \<in> Traces Spec\<close>
  oops


lemma dali_trace_concurrent_1:
  \<open>map(ev) [
      invUpdate (T0,K0,V0),
      invUpdate (T1,K1,V1),
      resUpdate T0,
      resUpdate T1,
      crash,
      invRead (T2,K1),
      resRead (T2,V1),
      invRead (T2,K0),
      resRead (T2,V0)
   ] \<in> Traces Dali\<close>
  oops


lemma dali_trace_concurrent_2:
  \<open>map(ev) [
      invUpdate (T0,K0,V0),
      invUpdate (T1,K1,V1),
      resUpdate T0,
      resUpdate T1,
      crash,
      invRead (T2,K1),
      resRead (T2,TNull),
      invRead (T2,K0),
      resRead (T2,V0)
   ] \<in> Traces Dali\<close>
  oops




end


end
