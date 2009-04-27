(*  Title:      JinjaThreads/Compiler/J1JVMBisim.thy
    Author:     Andreas Lochbihler
*)

header {* \isaheader{The weak bisimulation between intermediate language and JVM} *}

theory J1JVMBisim imports Execs begin

inductive bisim1 :: "'m prog \<Rightarrow> heap \<Rightarrow> expr1 \<Rightarrow> nat \<Rightarrow> (expr1 \<times> val list) \<Rightarrow> (val list \<times> val list \<times> pc \<times> addr option) \<Rightarrow> bool"
  and bisims1 :: "'m prog \<Rightarrow> heap \<Rightarrow> expr1 list \<Rightarrow> nat \<Rightarrow> (expr1 list \<times> val list) \<Rightarrow> (val list \<times> val list \<times> pc \<times> addr option) \<Rightarrow> bool"
  and bisim1_syntax :: "'m prog \<Rightarrow> expr1 \<Rightarrow> nat \<Rightarrow> heap \<Rightarrow> (expr1 \<times> val list) \<Rightarrow> (val list \<times> val list \<times> pc \<times> addr option) \<Rightarrow> bool" ("_,_,_,_ \<turnstile> _ \<leftrightarrow> _" [50, 0, 0, 0, 0, 50] 100)
  and bisims1_syntax :: "'m prog \<Rightarrow> expr1 list \<Rightarrow> nat \<Rightarrow> heap \<Rightarrow> (expr1 list \<times> val list) \<Rightarrow> (val list \<times> val list \<times> pc \<times> addr option) \<Rightarrow> bool" ("_,_,_,_ \<turnstile> _ [\<leftrightarrow>] _" [50, 0, 0, 0, 0, 50] 100)
  for P :: "'m prog" and  h :: heap
where
  "P, e, n, h \<turnstile> exs \<leftrightarrow> s \<equiv> bisim1 P h e n exs s"
| "P, es, n, h \<turnstile> esxs [\<leftrightarrow>] s \<equiv> bisims1 P h es n esxs s"

| bisim1Val2:
  "bsok e n \<Longrightarrow> P, e, n, h \<turnstile> (Val v, xs) \<leftrightarrow> (v # [], xs, length (compE2 e), None)"

| bisim1New:
  "P, new C, n, h \<turnstile> (new C, xs) \<leftrightarrow> ([], xs, 0, None)"

| bisim1NewThrow:
  "P, new C, n, h \<turnstile> (THROW OutOfMemory, xs) \<leftrightarrow> ([], xs, 0, \<lfloor>addr_of_sys_xcpt OutOfMemory\<rfloor>)"


| bisim1NewArray:
  "P, e, n, h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, xcp) \<Longrightarrow> P, newA T\<lfloor>e\<rceil>, n, h \<turnstile> (newA T\<lfloor>e'\<rceil>, xs) \<leftrightarrow> (stk, loc, pc, xcp)"

| bisim1NewArrayThrow:
  "P, e, n, h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>) \<Longrightarrow> P, newA T\<lfloor>e\<rceil>, n, h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)"

| bisim1NewArrayNegative:
  "bsok e n \<Longrightarrow> P, newA T\<lfloor>e\<rceil>, n, h \<turnstile> (THROW NegativeArraySize, xs) \<leftrightarrow> ([v], xs, length (compE2 e), \<lfloor>addr_of_sys_xcpt NegativeArraySize\<rfloor>)"

| bisim1NewArrayFail:
  "bsok e n \<Longrightarrow> P, newA T\<lfloor>e\<rceil>, n, h \<turnstile> (THROW OutOfMemory, xs) \<leftrightarrow> ([v], xs, length (compE2 e), \<lfloor>addr_of_sys_xcpt OutOfMemory\<rfloor>)"


| bisim1Cast:
  "P, e, n, h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, xcp) \<Longrightarrow> P, Cast T e, n, h \<turnstile> (Cast T e', xs) \<leftrightarrow> (stk, loc, pc, xcp)"

| bisim1CastThrow:
  "P, e, n, h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>) \<Longrightarrow> P, Cast T e, n, h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)"

| bisim1CastFail:
  "bsok e n \<Longrightarrow> P, Cast T e, n, h \<turnstile> (THROW ClassCast, xs) \<leftrightarrow> ([v], xs, length (compE2 e), \<lfloor>addr_of_sys_xcpt ClassCast\<rfloor>)"


| bisim1Val: "P, Val v, n, h \<turnstile> (Val v, xs) \<leftrightarrow> ([], xs, 0, None)"

| bisim1Var: "P, Var V, n, h \<turnstile> (Var V, xs) \<leftrightarrow> ([], xs, 0, None)"


| bisim1BinOp1:
  "\<lbrakk> P, e1, n, h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, xcp); bsok e2 n \<rbrakk>
  \<Longrightarrow> P, e1\<guillemotleft>bop\<guillemotright>e2, n, h \<turnstile> (e'\<guillemotleft>bop\<guillemotright>e2, xs) \<leftrightarrow> (stk, loc, pc, xcp)"

| bisim1BinOp2:
  "\<lbrakk> P, e2, n, h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, xcp); bsok e1 n \<rbrakk>
  \<Longrightarrow> P, e1\<guillemotleft>bop\<guillemotright>e2, n, h \<turnstile> (Val v1 \<guillemotleft>bop\<guillemotright> e', xs) \<leftrightarrow> (stk @ [v1], loc, length (compE2 e1) + pc, xcp)"

| bisim1BinOpThrow1:
  "\<lbrakk> P, e1, n, h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>); bsok e2 n \<rbrakk>
  \<Longrightarrow> P, e1\<guillemotleft>bop\<guillemotright>e2, n, h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)"

| bisim1BinOpThrow2:
  "\<lbrakk> P, e2, n, h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>); bsok e1 n \<rbrakk>
  \<Longrightarrow> P, e1\<guillemotleft>bop\<guillemotright>e2, n, h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk @ [v1], loc, length (compE2 e1) + pc, \<lfloor>a\<rfloor>)"


| bisim1LAss1:
  "P, e, n, h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, xcp) \<Longrightarrow> P, V:=e, n, h \<turnstile> (V:=e', xs) \<leftrightarrow> (stk, loc, pc, xcp)"

| bisim1LAss2:
  "bsok e n \<Longrightarrow> P, V:=e, n, h \<turnstile> (unit, xs) \<leftrightarrow> ([], xs, Suc (length (compE2 e)), None)"

| bisim1LAssThrow:
  "P, e, n, h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>) \<Longrightarrow> P, V:=e, n, h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)"

| bisim1AAcc1:
  "\<lbrakk> P, a, n, h \<turnstile> (a', xs) \<leftrightarrow> (stk, loc, pc, xcp); bsok i n \<rbrakk>
  \<Longrightarrow> P, a\<lfloor>i\<rceil>, n, h \<turnstile> (a'\<lfloor>i\<rceil>, xs) \<leftrightarrow> (stk, loc, pc, xcp)"

| bisim1AAcc2:
  "\<lbrakk> P, i, n, h \<turnstile> (i', xs) \<leftrightarrow> (stk, loc, pc, xcp); bsok a n \<rbrakk>
  \<Longrightarrow> P, a\<lfloor>i\<rceil>, n, h \<turnstile> (Val v\<lfloor>i'\<rceil>, xs) \<leftrightarrow> (stk @ [v], loc, length (compE2 a) + pc, xcp)"

| bisim1AAccThrow1:
  "\<lbrakk> P, a, n, h \<turnstile> (Throw ad, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>ad\<rfloor>); bsok i n \<rbrakk>
  \<Longrightarrow> P, a\<lfloor>i\<rceil>, n, h \<turnstile> (Throw ad, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>ad\<rfloor>)"

| bisim1AAccThrow2:
  "\<lbrakk> P, i, n, h \<turnstile> (Throw ad, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>ad\<rfloor>); bsok a n \<rbrakk>
  \<Longrightarrow> P, a\<lfloor>i\<rceil>, n, h \<turnstile> (Throw ad, xs) \<leftrightarrow> (stk @ [v], loc, length (compE2 a) + pc, \<lfloor>ad\<rfloor>)"

| bisim1AAccNull:
  "\<lbrakk> bsok a n; bsok i n \<rbrakk>
  \<Longrightarrow> P, a\<lfloor>i\<rceil>, n, h \<turnstile> (THROW NullPointer, xs) \<leftrightarrow> ([v, Null], xs, length (compE2 a) + length (compE2 i), \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>)"

| bisim1AAccBounds:
  "\<lbrakk> bsok a n; bsok i n \<rbrakk>
  \<Longrightarrow> P, a\<lfloor>i\<rceil>, n, h \<turnstile> (THROW ArrayIndexOutOfBounds, xs) \<leftrightarrow> ([v, Addr a'], xs, length (compE2 a) + length (compE2 i), \<lfloor>addr_of_sys_xcpt ArrayIndexOutOfBounds\<rfloor>)"


| bisim1AAss1:
  "\<lbrakk> P, a, n, h \<turnstile> (a', xs) \<leftrightarrow> (stk, loc, pc, xcp); bsok i n; bsok e n \<rbrakk>
  \<Longrightarrow> P, a\<lfloor>i\<rceil> := e, n, h \<turnstile> (a'\<lfloor>i\<rceil> := e, xs) \<leftrightarrow> (stk, loc, pc, xcp)"

| bisim1AAss2:
  "\<lbrakk> P, i, n, h \<turnstile> (i', xs) \<leftrightarrow> (stk, loc, pc, xcp); bsok a n; bsok e n \<rbrakk>
  \<Longrightarrow> P, a\<lfloor>i\<rceil> := e, n, h \<turnstile> (Val v\<lfloor>i'\<rceil> := e, xs) \<leftrightarrow> (stk @ [v], loc, length (compE2 a) + pc, xcp)"

| bisim1AAss3:
  "\<lbrakk> P, e, n, h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, xcp); bsok a n; bsok i n \<rbrakk>
  \<Longrightarrow> P, a\<lfloor>i\<rceil> := e, n, h \<turnstile> (Val v\<lfloor>Val v'\<rceil> := e', xs) \<leftrightarrow> (stk @ [v', v], loc, length (compE2 a) + length (compE2 i) + pc, xcp)"

| bisim1AAssThrow1:
  "\<lbrakk> P, a, n, h \<turnstile> (Throw ad, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>ad\<rfloor>); bsok i n; bsok e n \<rbrakk>
  \<Longrightarrow> P, a\<lfloor>i\<rceil> := e, n, h \<turnstile> (Throw ad, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>ad\<rfloor>)"

| bisim1AAssThrow2:
  "\<lbrakk> P, i, n, h \<turnstile> (Throw ad, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>ad\<rfloor>); bsok a n; bsok e n \<rbrakk>
  \<Longrightarrow> P, a\<lfloor>i\<rceil> := e, n, h \<turnstile> (Throw ad, xs) \<leftrightarrow> (stk @ [v], loc, length (compE2 a) + pc, \<lfloor>ad\<rfloor>)"

| bisim1AAssThrow3:
  "\<lbrakk> P, e, n, h \<turnstile> (Throw ad, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>ad\<rfloor>); bsok a n; bsok i n \<rbrakk>
  \<Longrightarrow> P, a\<lfloor>i\<rceil> := e, n, h \<turnstile> (Throw ad, xs) \<leftrightarrow> (stk @ [v', v], loc, length (compE2 a) + length (compE2 i) + pc, \<lfloor>ad\<rfloor>)"

| bisim1AAssNull:
  "\<lbrakk> bsok a n; bsok i n; bsok e n \<rbrakk>
  \<Longrightarrow> P, a\<lfloor>i\<rceil> := e, n, h \<turnstile> (THROW NullPointer, xs) \<leftrightarrow> ([v', v, Null], xs, length (compE2 a) + length (compE2 i) + length (compE2 e), \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>)"

| bisim1AAssBounds:
  "\<lbrakk> bsok a n; bsok i n; bsok e n \<rbrakk>
  \<Longrightarrow> P, a\<lfloor>i\<rceil> := e, n, h \<turnstile> (THROW ArrayIndexOutOfBounds, xs) \<leftrightarrow> ([v', v, Addr a'], xs, length (compE2 a) + length (compE2 i) + length (compE2 e), \<lfloor>addr_of_sys_xcpt ArrayIndexOutOfBounds\<rfloor>)"

| bisim1AAssStore:
  "\<lbrakk> bsok a n; bsok i n; bsok e n \<rbrakk>
  \<Longrightarrow> P, a\<lfloor>i\<rceil> := e, n, h \<turnstile> (THROW ArrayStore, xs) \<leftrightarrow> ([v', v, Addr a'], xs, length (compE2 a) + length (compE2 i) + length (compE2 e), \<lfloor>addr_of_sys_xcpt ArrayStore\<rfloor>)"

| bisim1AAss4:
  "\<lbrakk> bsok a n; bsok i n; bsok e n \<rbrakk>
  \<Longrightarrow> P, a\<lfloor>i\<rceil> := e, n, h \<turnstile> (unit, xs) \<leftrightarrow> ([], xs, Suc (length (compE2 a) + length (compE2 i) + length (compE2 e)), None)"


| bisim1ALength: 
  "P, a, n, h \<turnstile> (a', xs) \<leftrightarrow> (stk, loc, pc, xcp)
  \<Longrightarrow> P, a\<bullet>length, n, h \<turnstile> (a'\<bullet>length, xs) \<leftrightarrow> (stk, loc, pc, xcp)"

| bisim1ALengthThrow:
  "P, a, n, h \<turnstile> (Throw ad, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>ad\<rfloor>)
  \<Longrightarrow> P, a\<bullet>length, n, h \<turnstile> (Throw ad, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>ad\<rfloor>)"


| bisim1ALengthNull:
  "bsok a n \<Longrightarrow> P, a\<bullet>length, n, h \<turnstile> (THROW NullPointer, xs) \<leftrightarrow> ([Null], xs, length (compE2 a), \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>)"


| bisim1FAcc: 
  "P, e, n, h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, xcp)
  \<Longrightarrow> P, e\<bullet>F{D}, n, h \<turnstile> (e'\<bullet>F{D}, xs) \<leftrightarrow> (stk, loc, pc, xcp)"

| bisim1FAccThrow:
  "P, e, n, h \<turnstile> (Throw ad, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>ad\<rfloor>)
  \<Longrightarrow> P, e\<bullet>F{D}, n, h \<turnstile> (Throw ad, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>ad\<rfloor>)"

| bisim1FAccNull:
  "bsok e n \<Longrightarrow> P, e\<bullet>F{D}, n, h \<turnstile> (THROW NullPointer, xs) \<leftrightarrow> ([Null], xs, length (compE2 e), \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>)"


| bisim1FAss1: 
  "\<lbrakk> P, e, n, h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, xcp); bsok e2 n \<rbrakk>
  \<Longrightarrow> P, e\<bullet>F{D} := e2, n, h \<turnstile> (e'\<bullet>F{D} := e2, xs) \<leftrightarrow> (stk, loc, pc, xcp)"

| bisim1FAss2: 
  "\<lbrakk> P, e2, n, h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, xcp); bsok e n \<rbrakk>
  \<Longrightarrow> P, e\<bullet>F{D} := e2, n, h \<turnstile> (Val v\<bullet>F{D} := e', xs) \<leftrightarrow> (stk @ [v], loc, length (compE2 e) + pc, xcp)"

| bisim1FAssThrow1:
  "\<lbrakk> P, e, n, h \<turnstile> (Throw ad, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>ad\<rfloor>); bsok e2 n \<rbrakk>
  \<Longrightarrow> P, e\<bullet>F{D} := e2, n, h \<turnstile> (Throw ad, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>ad\<rfloor>)"

| bisim1FAssThrow2:
  "\<lbrakk> P, e2, n, h \<turnstile> (Throw ad, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>ad\<rfloor>); bsok e n \<rbrakk>
  \<Longrightarrow> P, e\<bullet>F{D} := e2, n, h \<turnstile> (Throw ad, xs) \<leftrightarrow> (stk @ [v], loc, length (compE2 e) + pc, \<lfloor>ad\<rfloor>)"

| bisim1FAssNull:
  "\<lbrakk> bsok e n; bsok e2 n \<rbrakk>
   \<Longrightarrow> P, e\<bullet>F{D} := e2, n, h \<turnstile> (THROW NullPointer, xs) \<leftrightarrow> ([v, Null], xs, length (compE2 e) + length (compE2 e2), \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>)"

| bisim1FAss3:
  "\<lbrakk> bsok e n; bsok e2 n \<rbrakk>
  \<Longrightarrow> P, e\<bullet>F{D} := e2, n, h \<turnstile> (unit, xs) \<leftrightarrow> ([], xs, Suc (length (compE2 e) + length (compE2 e2)), None)"


| bisim1Call1:
  "\<lbrakk> P, obj, n, h \<turnstile> (obj', xs) \<leftrightarrow> (stk, loc, pc, xcp); bsoks ps n \<rbrakk>
  \<Longrightarrow> P, obj\<bullet>M(ps), n, h \<turnstile> (obj'\<bullet>M(ps), xs) \<leftrightarrow> (stk, loc, pc, xcp)"

| bisim1CallParams:
  "\<lbrakk> P, ps, n, h \<turnstile> (ps', xs) [\<leftrightarrow>] (stk, loc, pc, xcp); bsok obj n \<rbrakk>
  \<Longrightarrow> P, obj\<bullet>M(ps), n, h \<turnstile> (Val v\<bullet>M(ps'), xs) \<leftrightarrow> (stk @ [v], loc, length (compE2 obj) +  pc, xcp)"

| bisim1CallThrowObj:
  "\<lbrakk> P, obj, n, h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>); bsoks ps n \<rbrakk>
  \<Longrightarrow> P, obj\<bullet>M(ps), n, h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)"

| bisim1CallThrowParams:
  "\<lbrakk> P, ps, n, h \<turnstile> (map Val vs @ Throw a # ps', xs) [\<leftrightarrow>] (stk, loc, pc, \<lfloor>a\<rfloor>); bsok obj n \<rbrakk>
  \<Longrightarrow> P, obj\<bullet>M(ps), n, h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk @ [v], loc, length (compE2 obj) + pc, \<lfloor>a\<rfloor>)"

| bisim1CallThrow:
  "\<lbrakk> length ps = length vs; bsok obj n; bsoks ps n \<rbrakk>
  \<Longrightarrow> P, obj\<bullet>M(ps), n, h \<turnstile> (Throw a, xs) \<leftrightarrow> (vs @ [v], xs, length (compE2 obj) + length (compEs2 ps), \<lfloor>a\<rfloor>)"

| bisim1BlockSome1:
  "bsok e (Suc V) \<Longrightarrow> P, {V:T=\<lfloor>v\<rfloor>; e}\<^bsub>False\<^esub>, V, h \<turnstile> ({V:T=\<lfloor>v\<rfloor>; e}\<^bsub>False\<^esub>, xs) \<leftrightarrow> ([], xs, 0, None)"

| bisim1BlockSome2:
  "bsok e (Suc V) \<Longrightarrow> P, {V:T=\<lfloor>v\<rfloor>; e}\<^bsub>False\<^esub>, V, h \<turnstile> ({V:T=\<lfloor>v\<rfloor>; e}\<^bsub>False\<^esub>, xs) \<leftrightarrow> ([v], xs, Suc 0, None)"

| bisim1BlockSome3:
  "\<lbrakk> P,e,Suc V,h \<turnstile> (e',xs[V := v]) \<leftrightarrow> (stk, loc, pc, xcp) \<rbrakk>
  \<Longrightarrow> P, {V:T=\<lfloor>v\<rfloor>; e}\<^bsub>False\<^esub>, V, h \<turnstile> ({V:T=\<lfloor>v\<rfloor>; e'}\<^bsub>False\<^esub>, xs) \<leftrightarrow> (stk, loc, Suc (Suc pc), xcp)"

| bisim1BlockSome4:
  "\<lbrakk> P, e, Suc V, h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, xcp) \<rbrakk>
  \<Longrightarrow> P, {V:T=\<lfloor>v\<rfloor>; e}\<^bsub>False\<^esub>, V, h \<turnstile> ({V:T=None; e'}\<^bsub>False\<^esub>, xs) \<leftrightarrow> (stk, loc, Suc (Suc pc), xcp)"

| bisim1BlockThrowSome:
  "P, e, Suc V, h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)
  \<Longrightarrow> P, {V:T=\<lfloor>v\<rfloor>; e}\<^bsub>False\<^esub>, V, h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, Suc (Suc pc), \<lfloor>a\<rfloor>)"

| bisim1BlockNone:
  "P, e, Suc V, h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, xcp)
  \<Longrightarrow> P, {V:T=None; e}\<^bsub>False\<^esub>, V, h \<turnstile> ({V:T=None; e'}\<^bsub>False\<^esub>, xs) \<leftrightarrow> (stk, loc, pc, xcp)"

| bisim1BlockThrowNone:
  "P, e, Suc V, h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)
   \<Longrightarrow> P, {V:T=None; e}\<^bsub>False\<^esub>, V, h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)"


| bisim1Sync1:
  "\<lbrakk> P, e1, V, h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, xcp); bsok e2 (Suc V) \<rbrakk>
  \<Longrightarrow> P, sync\<^bsub>V\<^esub> (e1) e2, V, h \<turnstile> (sync\<^bsub>V\<^esub> (e') e2, xs) \<leftrightarrow> (stk, loc, pc, xcp)"

| bisim1Sync2:
  "\<lbrakk> bsok e1 V; bsok e2 (Suc V) \<rbrakk>
  \<Longrightarrow> P, sync\<^bsub>V\<^esub> (e1) e2, V, h \<turnstile> (sync\<^bsub>V\<^esub> (Val v) e2, xs) \<leftrightarrow> ([], xs[V := v], Suc (length (compE2 e1)), None)"

| bisim1Sync3:
  "\<lbrakk> bsok e1 V; bsok e2 (Suc V) \<rbrakk>
  \<Longrightarrow> P, sync\<^bsub>V\<^esub> (e1) e2, V, h \<turnstile> (sync\<^bsub>V\<^esub> (Val v) e2, xs) \<leftrightarrow> ([v], xs[V := v], Suc (Suc (length (compE2 e1))), None)"

| bisim1Sync4:
  "\<lbrakk> P, e2, Suc V, h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, xcp); bsok e1 V \<rbrakk>
  \<Longrightarrow> P, sync\<^bsub>V\<^esub> (e1) e2, V, h \<turnstile> (insync\<^bsub>V\<^esub> (a) e', xs) \<leftrightarrow> (stk, loc, Suc (Suc (Suc (length (compE2 e1) + pc))), xcp)"

| bisim1Sync5:
  "\<lbrakk> bsok e1 V; bsok e2 (Suc V) \<rbrakk>
  \<Longrightarrow> P, sync\<^bsub>V\<^esub> (e1) e2, V, h \<turnstile> (insync\<^bsub>V\<^esub> (a) Val v, xs) \<leftrightarrow> ([xs ! V, v], xs, 4 + length (compE2 e1) + length (compE2 e2), None)"

| bisim1Sync6:
  "\<lbrakk> bsok e1 V; bsok e2 (Suc V) \<rbrakk>
  \<Longrightarrow> P, sync\<^bsub>V\<^esub> (e1) e2, V, h \<turnstile> (Val v, xs) \<leftrightarrow> ([v], xs, 5 + length (compE2 e1) + length (compE2 e2), None)"

| bisim1Sync7:
  "\<lbrakk> bsok e1 V; bsok e2 (Suc V) \<rbrakk>
  \<Longrightarrow> P, sync\<^bsub>V\<^esub> (e1) e2, V, h \<turnstile> (insync\<^bsub>V\<^esub> (a) Throw a', xs) \<leftrightarrow> ([Addr a'], xs, 6 + length (compE2 e1) + length (compE2 e2), None)"

| bisim1Sync8:
  "\<lbrakk> bsok e1 V; bsok e2 (Suc V) \<rbrakk>
  \<Longrightarrow> P, sync\<^bsub>V\<^esub> (e1) e2, V, h \<turnstile> (insync\<^bsub>V\<^esub> (a) Throw a', xs) \<leftrightarrow>
        ([xs ! V, Addr a'], xs, 7 + length (compE2 e1) + length (compE2 e2), None)"

| bisim1Sync9:
  "\<lbrakk> bsok e1 V; bsok e2 (Suc V) \<rbrakk>
  \<Longrightarrow> P, sync\<^bsub>V\<^esub> (e1) e2, V, h \<turnstile> (Throw a, xs) \<leftrightarrow> ([Addr a], xs, 8 + length (compE2 e1) + length (compE2 e2), None)"

| bisim1Sync10:
  "\<lbrakk> bsok e1 V; bsok e2 (Suc V) \<rbrakk>
  \<Longrightarrow> P, sync\<^bsub>V\<^esub> (e1) e2, V, h \<turnstile> (Throw a, xs) \<leftrightarrow> ([Addr a], xs, 8 + length (compE2 e1) + length (compE2 e2), \<lfloor>a\<rfloor>)"

| bisim1Sync11:
  "\<lbrakk> bsok e1 V; bsok e2 (Suc V) \<rbrakk>
  \<Longrightarrow> P, sync\<^bsub>V\<^esub> (e1) e2, V, h \<turnstile> (THROW NullPointer, xs) \<leftrightarrow> ([Null], xs, Suc (Suc (length (compE2 e1))), \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>)"

| bisim1Sync12:
  "\<lbrakk> bsok e1 V; bsok e2 (Suc V) \<rbrakk>
  \<Longrightarrow> P, sync\<^bsub>V\<^esub> (e1) e2, V, h \<turnstile> (THROW NullPointer, xs) \<leftrightarrow> ([Null, v], xs, 4 + length (compE2 e1) + length (compE2 e2), \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>)"

| bisim1Sync13:
  "\<lbrakk> bsok e1 V; bsok e2 (Suc V) \<rbrakk>
  \<Longrightarrow> P, sync\<^bsub>V\<^esub> (e1) e2, V, h \<turnstile> (THROW IllegalMonitorState, xs) \<leftrightarrow> ([v', v], xs, 4 + length (compE2 e1) + length (compE2 e2), \<lfloor>addr_of_sys_xcpt IllegalMonitorState\<rfloor>)"

| bisim1Sync14:
  "\<lbrakk> bsok e1 V; bsok e2 (Suc V) \<rbrakk>
  \<Longrightarrow> P, sync\<^bsub>V\<^esub> (e1) e2, V, h \<turnstile> (THROW IllegalMonitorState, xs) \<leftrightarrow>
        ([v, Addr a'], xs, 7 + length (compE2 e1) + length (compE2 e2), \<lfloor>addr_of_sys_xcpt IllegalMonitorState\<rfloor>)"

| bisim1Sync15:
  "\<lbrakk> bsok e1 V; bsok e2 (Suc V) \<rbrakk>
  \<Longrightarrow> P, sync\<^bsub>V\<^esub> (e1) e2, V, h \<turnstile> (THROW NullPointer, xs) \<leftrightarrow>
        ([Null, Addr a'], xs, 7 + length (compE2 e1) + length (compE2 e2), \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>)"


| bisim1SyncThrow:
  "\<lbrakk> P, e1, V, h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>); bsok e2 (Suc V) \<rbrakk>
  \<Longrightarrow> P, sync\<^bsub>V\<^esub> (e1) e2, V, h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)"


| bisim1Seq1:
  "\<lbrakk> P, e1, n, h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, xcp); bsok e2 n \<rbrakk> \<Longrightarrow> P, e1;;e2, n, h \<turnstile> (e';;e2, xs) \<leftrightarrow> (stk, loc, pc, xcp)"

| bisim1SeqThrow1:
  "\<lbrakk> P, e1, n, h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>); bsok e2 n \<rbrakk> \<Longrightarrow> P, e1;;e2, n, h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)"

| bisim1Seq2:
  "\<lbrakk> P, e2, n, h \<turnstile> exs \<leftrightarrow> (stk, loc, pc, xcp); bsok e1 n \<rbrakk>
  \<Longrightarrow> P, e1;;e2, n, h \<turnstile> exs \<leftrightarrow> (stk, loc, Suc (length (compE2 e1) + pc), xcp)"


| bisim1Cond1:
  "\<lbrakk> P, e, n, h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, xcp); bsok e1 n; bsok e2 n \<rbrakk>
  \<Longrightarrow> P, if (e) e1 else e2, n, h \<turnstile> (if (e') e1 else e2, xs) \<leftrightarrow> (stk, loc, pc, xcp)"

| bisim1CondThen:
  "\<lbrakk> P, e1, n, h \<turnstile> exs \<leftrightarrow> (stk, loc, pc, xcp); bsok e n; bsok e2 n \<rbrakk>
  \<Longrightarrow> P, if (e) e1 else e2, n, h \<turnstile> exs \<leftrightarrow> (stk, loc, Suc (length (compE2 e) + pc), xcp)"

| bisim1CondElse:
  "\<lbrakk> P, e2, n, h \<turnstile> exs \<leftrightarrow> (stk, loc, pc, xcp); bsok e n; bsok e1 n \<rbrakk>
  \<Longrightarrow> P, if (e) e1 else e2, n, h \<turnstile> exs \<leftrightarrow> (stk, loc, Suc (Suc (length (compE2 e) + length (compE2 e1) +  pc)), xcp)"

| bisim1CondThrow:
  "\<lbrakk> P, e, n, h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>); bsok e1 n; bsok e2 n \<rbrakk>
  \<Longrightarrow> P, if (e) e1 else e2, n, h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)"


| bisim1While1:
  "\<lbrakk> bsok c n; bsok e n \<rbrakk> \<Longrightarrow> P, while (c) e, n, h \<turnstile> (while (c) e, xs) \<leftrightarrow> ([], xs, 0, None)"

| bisim1While3:
  "\<lbrakk> P, c, n, h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, xcp); bsok e n \<rbrakk>
  \<Longrightarrow> P, while (c) e, n, h \<turnstile> (if (e') (e;; while (c) e) else unit, xs) \<leftrightarrow> (stk, loc, pc, xcp)"

| bisim1While4:
  "\<lbrakk> P, e, n, h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, xcp); bsok c n \<rbrakk>
  \<Longrightarrow> P, while (c) e, n, h  \<turnstile> (e';; while (c) e, xs) \<leftrightarrow> (stk, loc, Suc (length (compE2 c) + pc), xcp)"

| bisim1While6:
  "\<lbrakk> bsok c n; bsok e n \<rbrakk> \<Longrightarrow> 
  P, while (c) e, n, h \<turnstile> (while (c) e, xs) \<leftrightarrow> ([], xs, Suc (Suc (length (compE2 c) + length (compE2 e))), None)"

| bisim1While7:
  "\<lbrakk> bsok c n; bsok e n \<rbrakk> \<Longrightarrow> 
  P, while (c) e, n, h \<turnstile> (unit, xs) \<leftrightarrow> ([], xs, Suc (Suc (Suc (length (compE2 c) + length (compE2 e)))), None)"

| bisim1WhileThrow1:
  "\<lbrakk> P, c, n, h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>); bsok e n \<rbrakk>
  \<Longrightarrow> P, while (c) e, n, h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)"

| bisim1WhileThrow2:
  "\<lbrakk> P, e, n, h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>); bsok c n \<rbrakk>
   \<Longrightarrow> P, while (c) e, n, h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, Suc (length (compE2 c) + pc), \<lfloor>a\<rfloor>)"


| bisim1Throw1:
  "P, e, n, h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, xcp) \<Longrightarrow> P, throw e, n, h \<turnstile> (throw e', xs) \<leftrightarrow> (stk, loc, pc, xcp)"

| bisim1Throw2:
  "\<lbrakk> bsok e n \<rbrakk> \<Longrightarrow> P, throw e, n, h \<turnstile> (Throw a, xs) \<leftrightarrow> ([Addr a], xs, length (compE2 e), \<lfloor>a\<rfloor>)"

| bisim1ThrowNull:
  "bsok e n \<Longrightarrow> P, throw e, n, h \<turnstile> (THROW NullPointer, xs) \<leftrightarrow> ([Null], xs, length (compE2 e), \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>)"

| bisim1ThrowThrow:
  "P, e, n, h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>) \<Longrightarrow> P, throw e, n, h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)"


| bisim1Try:
  "\<lbrakk> P, e, V, h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, xcp); bsok e2 (Suc V) \<rbrakk>
   \<Longrightarrow> P, try e catch(C V) e2, V, h \<turnstile> (try e' catch(C V) e2, xs) \<leftrightarrow> (stk, loc, pc, xcp)"

| bisim1TryCatch1:
  "\<lbrakk> P, e, V, h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>); h a = \<lfloor>Obj C' fs\<rfloor>; P \<turnstile> C' \<preceq>\<^sup>* C; bsok e2 (Suc V) \<rbrakk>
  \<Longrightarrow> P, try e catch(C V) e2, V, h \<turnstile> ({V:Class C=None; e2}\<^bsub>False\<^esub>, xs[V := Addr a]) \<leftrightarrow> ([Addr a], loc, Suc (length (compE2 e)), None)"

| bisim1TryCatch2:
  "\<lbrakk> P, e2, Suc V, h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, xcp); bsok e V \<rbrakk>
   \<Longrightarrow> P, try e catch(C V) e2, V, h \<turnstile> ({V:Class C=None; e'}\<^bsub>False\<^esub>, xs) \<leftrightarrow> (stk, loc, Suc (Suc (length (compE2 e) + pc)), xcp)"

| bisim1TryFail:
  "\<lbrakk> P, e, V, h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>); h a = \<lfloor>Obj C' fs\<rfloor>; \<not> P \<turnstile> C' \<preceq>\<^sup>* C; bsok e2 (Suc V) \<rbrakk> 
  \<Longrightarrow> P, try e catch(C V) e2, V, h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)"

| bisim1TryCatchThrow:
  "\<lbrakk> P, e2, Suc V, h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>); bsok e V \<rbrakk>
   \<Longrightarrow> P, try e catch(C V) e2, V, h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, Suc (Suc (length (compE2 e) + pc)), \<lfloor>a\<rfloor>)"

| bisims1Nil: "P, [], n, h \<turnstile> ([], xs) [\<leftrightarrow>] ([], xs, 0, None)"

| bisims1List1:
  "\<lbrakk> P, e, n, h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, xcp); bsoks es n \<rbrakk> \<Longrightarrow> P, e#es, n, h \<turnstile> (e'#es, xs) [\<leftrightarrow>] (stk, loc, pc, xcp)"

| bisims1List2:
  "\<lbrakk> P, es, n, h \<turnstile> (es', xs) [\<leftrightarrow>] (stk, loc, pc, xcp); bsok e n \<rbrakk>
  \<Longrightarrow> P, e#es, n, h \<turnstile> (Val v # es', xs) [\<leftrightarrow>] (stk @ [v], loc, length (compE2 e) + pc, xcp)"


inductive_cases bisim1_cases:
  "P,e,n,h \<turnstile> (Val v, xs) \<leftrightarrow> (stk, loc, pc, xcp)"


lemma bisim1_refl: "bsok e n \<Longrightarrow> P,e,n,h \<turnstile> (e, xs) \<leftrightarrow> ([], xs, 0, None)"
  and bisims1_refl: "bsoks es n \<Longrightarrow> P,es,n,h \<turnstile> (es, xs) [\<leftrightarrow>] ([], xs, 0, None)"
apply(induct e and es arbitrary: n and n)
apply(auto intro: bisim1_bisims1.intros simp add: nat_fun_sum_eq_conv)
apply(case_tac option)
apply(auto intro: bisim1_bisims1.intros split: split_if_asm)
done

lemma bisim1_B: "P,e,n,h \<turnstile> (e', xs) \<leftrightarrow> s \<Longrightarrow> \<B> e n \<and> \<B> e' n"
  and bisims1_Bs: "P,es,n,h \<turnstile> (es', xs) [\<leftrightarrow>] s \<Longrightarrow> \<B>s es n \<and> \<B>s es' n"
apply(induct exs\<equiv>"(e', xs)" s and esxs\<equiv>"(es', xs)" s arbitrary: e' xs and es' xs rule: bisim1_bisims1.inducts)
apply(auto simp add: bsok_def bsoks_def)
apply blast+
done

lemma bisim1_bsok: "P,e,n,h \<turnstile> exs \<leftrightarrow> s \<Longrightarrow> bsok e n"
  and bisims1_bsoks: "P,es,n,h \<turnstile> esxs [\<leftrightarrow>] s \<Longrightarrow> bsoks es n"
apply(induct rule: bisim1_bisims1.inducts)
apply(auto)
done

lemma bsok_bisim_refl_conv: "bsok e n \<longleftrightarrow> (\<forall>xs. P,e,n,h \<turnstile> (e, xs) \<leftrightarrow> ([],xs,0,None))"
by(auto intro: bisim1_refl bisim1_bsok)

lemma bsoks_bisims_refl_conv: "bsoks es n \<longleftrightarrow> (\<forall>xs. P,es,n,h \<turnstile> (es, xs) [\<leftrightarrow>] ([],xs,0,None))"
by(auto intro: bisims1_refl bisims1_bsoks)

lemma bisim1_noRetBlock: "P,e,n,h \<turnstile> (e', xs) \<leftrightarrow> s \<Longrightarrow> noRetBlock e \<and> noRetBlock e'"
  and bisims1_noRetBlocks: "P,es,n,h \<turnstile> (es', xs) [\<leftrightarrow>] s \<Longrightarrow> noRetBlocks es \<and> noRetBlocks es'"
apply(induct e n exs\<equiv>"(e', xs)" s and es n esxs\<equiv>"(es', xs)" s arbitrary: e' xs and es' xs rule: bisim1_bisims1.inducts)
apply(auto simp add: bsok_def bsoks_def)
apply blast+
done

lemma bisims1_lengthD: "P, es, n, h \<turnstile> (es', xs) [\<leftrightarrow>] s \<Longrightarrow> length es = length es'"
apply(induct es arbitrary: es' s)
apply(auto elim: bisims1.cases)
done

inductive bisim1' :: "'m prog \<Rightarrow> heap \<Rightarrow> expr1 \<Rightarrow> nat \<Rightarrow> (expr1 \<times> val list) \<Rightarrow> (val list \<times> val list \<times> pc \<times> addr option) \<Rightarrow> bool"
  and bisims1' :: "'m prog \<Rightarrow> heap \<Rightarrow> expr1 list \<Rightarrow> nat \<Rightarrow> (expr1 list \<times> val list) \<Rightarrow> (val list \<times> val list \<times> pc \<times> addr option) \<Rightarrow> bool"
  and bisim1'_syntax :: "'m prog \<Rightarrow> expr1 \<Rightarrow> nat \<Rightarrow> heap \<Rightarrow> (expr1 \<times> val list) \<Rightarrow> (val list \<times> val list \<times> pc \<times> addr option) \<Rightarrow> bool" ("_,_,_,_ \<turnstile>' _ \<leftrightarrow> _" [50, 0, 0, 0, 0, 50] 100)
  and bisims1'_syntax :: "'m prog \<Rightarrow> expr1 list \<Rightarrow> nat \<Rightarrow> heap \<Rightarrow> (expr1 list \<times> val list) \<Rightarrow> (val list \<times> val list \<times> pc \<times> addr option) \<Rightarrow> bool" ("_,_,_,_ \<turnstile>' _ [\<leftrightarrow>] _" [50, 0, 0, 0, 0, 50] 100)
  for P :: "'m prog" and  h :: heap
where
  "P, e, n, h \<turnstile>' exs \<leftrightarrow> s \<equiv> bisim1' P h e n exs s"
| "P, es, n, h \<turnstile>' esxs [\<leftrightarrow>] s \<equiv> bisims1' P h es n esxs s"

| bisim1Val2':
  "bsok e n \<Longrightarrow> P, e, n, h \<turnstile>' (Val v, xs) \<leftrightarrow> (v # [], xs, length (compE2 e), None)"

| bisim1New':
  "P, new C, n, h \<turnstile>' (new C, xs) \<leftrightarrow> ([], xs, 0, None)"

| bisim1NewThrow':
  "P, new C, n, h \<turnstile>' (THROW OutOfMemory, xs) \<leftrightarrow> ([], xs, 0, \<lfloor>addr_of_sys_xcpt OutOfMemory\<rfloor>)"


| bisim1NewArray':
  "\<lbrakk> P, e, n, h \<turnstile>' (e', xs) \<leftrightarrow> (stk, loc, pc, xcp); bsok e n \<rbrakk>
  \<Longrightarrow> P, newA T\<lfloor>e\<rceil>, n, h \<turnstile>' (newA T\<lfloor>e'\<rceil>, xs) \<leftrightarrow> (stk, loc, pc, xcp)"

| bisim1NewArrayThrow':
  "\<lbrakk> P, e, n, h \<turnstile>' (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>); bsok e n \<rbrakk>
  \<Longrightarrow> P, newA T\<lfloor>e\<rceil>, n, h \<turnstile>' (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)"

| bisim1NewArrayNegative':
  "\<lbrakk> \<And>xs. P, e, n, h \<turnstile>' (e, xs) \<leftrightarrow> ([], xs, 0, None); bsok e n \<rbrakk>
  \<Longrightarrow> P, newA T\<lfloor>e\<rceil>, n, h \<turnstile>' (THROW NegativeArraySize, xs) \<leftrightarrow> ([v], xs, length (compE2 e), \<lfloor>addr_of_sys_xcpt NegativeArraySize\<rfloor>)"

| bisim1NewArrayFail':
  "\<lbrakk> \<And>xs. P, e, n, h \<turnstile>' (e, xs) \<leftrightarrow> ([], xs, 0, None); bsok e n \<rbrakk>
  \<Longrightarrow> P, newA T\<lfloor>e\<rceil>, n, h \<turnstile>' (THROW OutOfMemory, xs) \<leftrightarrow> ([v], xs, length (compE2 e), \<lfloor>addr_of_sys_xcpt OutOfMemory\<rfloor>)"


| bisim1Cast':
  "\<lbrakk> P, e, n, h \<turnstile>' (e', xs) \<leftrightarrow> (stk, loc, pc, xcp); bsok e n \<rbrakk>
  \<Longrightarrow> P, Cast T e, n, h \<turnstile>' (Cast T e', xs) \<leftrightarrow> (stk, loc, pc, xcp)"

| bisim1CastThrow':
  "\<lbrakk> P, e, n, h \<turnstile>' (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>); bsok e n \<rbrakk>
  \<Longrightarrow> P, Cast T e, n, h \<turnstile>' (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)"

| bisim1CastFail':
  "\<lbrakk> \<And>xs. P, e, n, h \<turnstile>' (e, xs) \<leftrightarrow> ([], xs, 0, None); bsok e n \<rbrakk>
  \<Longrightarrow> P, Cast T e, n, h \<turnstile>' (THROW ClassCast, xs) \<leftrightarrow> ([v], xs, length (compE2 e), \<lfloor>addr_of_sys_xcpt ClassCast\<rfloor>)"


| bisim1Val': "P, Val v, n, h \<turnstile>' (Val v, xs) \<leftrightarrow> ([], xs, 0, None)"

| bisim1Var': "P, Var V, n, h \<turnstile>' (Var V, xs) \<leftrightarrow> ([], xs, 0, None)"


| bisim1BinOp1':
  "\<lbrakk> P, e1, n, h \<turnstile>' (e', xs) \<leftrightarrow> (stk, loc, pc, xcp); bsok e2 n;
     bsok e1 n; \<And>xs. P, e2, n, h \<turnstile>' (e2, xs) \<leftrightarrow> ([], xs, 0, None) \<rbrakk>
  \<Longrightarrow> P, e1\<guillemotleft>bop\<guillemotright>e2, n, h \<turnstile>' (e'\<guillemotleft>bop\<guillemotright>e2, xs) \<leftrightarrow> (stk, loc, pc, xcp)"

| bisim1BinOp2':
  "\<lbrakk> P, e2, n, h \<turnstile>' (e', xs) \<leftrightarrow> (stk, loc, pc, xcp);
     bsok e1 n; bsok e2 n; \<And>xs. P, e1, n, h \<turnstile>' (e1, xs) \<leftrightarrow> ([], xs, 0, None) \<rbrakk>
  \<Longrightarrow> P, e1\<guillemotleft>bop\<guillemotright>e2, n, h \<turnstile>' (Val v1 \<guillemotleft>bop\<guillemotright> e', xs) \<leftrightarrow> (stk @ [v1], loc, length (compE2 e1) + pc, xcp)"

| bisim1BinOpThrow1':
  "\<lbrakk> P, e1, n, h \<turnstile>' (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>);
     bsok e2 n; bsok e1 n; \<And>xs. P, e2, n, h \<turnstile>' (e2, xs) \<leftrightarrow> ([], xs, 0, None) \<rbrakk>
  \<Longrightarrow> P, e1\<guillemotleft>bop\<guillemotright>e2, n, h \<turnstile>' (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)"

| bisim1BinOpThrow2':
  "\<lbrakk> P, e2, n, h \<turnstile>' (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>);
     bsok e1 n; bsok e2 n; \<And>xs. P, e1, n, h \<turnstile>' (e1, xs) \<leftrightarrow> ([], xs, 0, None) \<rbrakk>
  \<Longrightarrow> P, e1\<guillemotleft>bop\<guillemotright>e2, n, h \<turnstile>' (Throw a, xs) \<leftrightarrow> (stk @ [v1], loc, length (compE2 e1) + pc, \<lfloor>a\<rfloor>)"


| bisim1LAss1':
  "\<lbrakk> P, e, n, h \<turnstile>' (e', xs) \<leftrightarrow> (stk, loc, pc, xcp); bsok e n \<rbrakk>
  \<Longrightarrow> P, V:=e, n, h \<turnstile>' (V:=e', xs) \<leftrightarrow> (stk, loc, pc, xcp)"

| bisim1LAss2':
  "\<lbrakk> bsok e n; \<And>xs. P, e, n, h \<turnstile>' (e, xs) \<leftrightarrow> ([], xs, 0, None) \<rbrakk>
   \<Longrightarrow> P, V:=e, n, h \<turnstile>' (unit, xs) \<leftrightarrow> ([], xs, Suc (length (compE2 e)), None)"

| bisim1LAssThrow':
  "\<lbrakk> P, e, n, h \<turnstile>' (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>); bsok e n \<rbrakk>
  \<Longrightarrow> P, V:=e, n, h \<turnstile>' (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)"


| bisim1AAcc1':
  "\<lbrakk> P, a, n, h \<turnstile>' (a', xs) \<leftrightarrow> (stk, loc, pc, xcp); bsok a n; \<And>xs. P, i, n, h \<turnstile>' (i, xs) \<leftrightarrow> ([], xs, 0, None); bsok i n \<rbrakk>
  \<Longrightarrow> P, a\<lfloor>i\<rceil>, n, h \<turnstile>' (a'\<lfloor>i\<rceil>, xs) \<leftrightarrow> (stk, loc, pc, xcp)"

| bisim1AAcc2':
  "\<lbrakk> P, i, n, h \<turnstile>' (i', xs) \<leftrightarrow> (stk, loc, pc, xcp); bsok i n; \<And>xs. P, a, n, h \<turnstile>' (a, xs) \<leftrightarrow> ([], xs, 0, None); bsok a n \<rbrakk>
  \<Longrightarrow> P, a\<lfloor>i\<rceil>, n, h \<turnstile>' (Val v\<lfloor>i'\<rceil>, xs) \<leftrightarrow> (stk @ [v], loc, length (compE2 a) + pc, xcp)"

| bisim1AAccThrow1':
  "\<lbrakk> P, a, n, h \<turnstile>' (Throw ad, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>ad\<rfloor>); bsok a n;
     \<And>xs. P, i, n, h \<turnstile>' (i, xs) \<leftrightarrow> ([], xs, 0, None); bsok i n \<rbrakk>
  \<Longrightarrow> P, a\<lfloor>i\<rceil>, n, h \<turnstile>' (Throw ad, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>ad\<rfloor>)"

| bisim1AAccThrow2':
  "\<lbrakk> P, i, n, h \<turnstile>' (Throw ad, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>ad\<rfloor>); bsok i n;
     \<And>xs. P, a, n, h \<turnstile>' (a, xs) \<leftrightarrow> ([], xs, 0, None); bsok a n \<rbrakk>
  \<Longrightarrow> P, a\<lfloor>i\<rceil>, n, h \<turnstile>' (Throw ad, xs) \<leftrightarrow> (stk @ [v], loc, length (compE2 a) + pc, \<lfloor>ad\<rfloor>)"

| bisim1AAccNull':
  "\<lbrakk> \<And>xs. P, a, n, h \<turnstile>' (a, xs) \<leftrightarrow> ([], xs, 0, None); bsok a n; \<And>xs. P, i, n, h \<turnstile>' (i, xs) \<leftrightarrow> ([], xs, 0, None); bsok i n \<rbrakk>
  \<Longrightarrow> P, a\<lfloor>i\<rceil>, n, h \<turnstile>' (THROW NullPointer, xs) \<leftrightarrow> ([v, Null], xs, length (compE2 a) + length (compE2 i), \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>)"

| bisim1AAccBounds':
  "\<lbrakk> \<And>xs. P, a, n, h \<turnstile>' (a, xs) \<leftrightarrow> ([], xs, 0, None); bsok a n; \<And>xs. P, i, n, h \<turnstile>' (i, xs) \<leftrightarrow> ([], xs, 0, None); bsok i n \<rbrakk>
  \<Longrightarrow> P, a\<lfloor>i\<rceil>, n, h \<turnstile>' (THROW ArrayIndexOutOfBounds, xs) \<leftrightarrow> ([v, Addr a'], xs, length (compE2 a) + length (compE2 i), \<lfloor>addr_of_sys_xcpt ArrayIndexOutOfBounds\<rfloor>)"


| bisim1AAss1':
  "\<lbrakk> P, a, n, h \<turnstile>' (a', xs) \<leftrightarrow> (stk, loc, pc, xcp); bsok a n;
     \<And>xs. P, i, n, h \<turnstile>' (i, xs) \<leftrightarrow> ([], xs, 0, None); bsok i n; 
     \<And>xs. P, e, n, h \<turnstile>' (e, xs) \<leftrightarrow> ([], xs, 0, None); bsok e n \<rbrakk>
  \<Longrightarrow> P, a\<lfloor>i\<rceil> := e, n, h \<turnstile>' (a'\<lfloor>i\<rceil> := e, xs) \<leftrightarrow> (stk, loc, pc, xcp)"

| bisim1AAss2':
  "\<lbrakk> P, i, n, h \<turnstile>' (i', xs) \<leftrightarrow> (stk, loc, pc, xcp); bsok i n;
     \<And>xs. P, a, n, h \<turnstile>' (a, xs) \<leftrightarrow> ([], xs, 0, None); bsok a n; 
     \<And>xs. P, e, n, h \<turnstile>' (e, xs) \<leftrightarrow> ([], xs, 0, None); bsok e n \<rbrakk>
  \<Longrightarrow> P, a\<lfloor>i\<rceil> := e, n, h \<turnstile>' (Val v\<lfloor>i'\<rceil> := e, xs) \<leftrightarrow> (stk @ [v], loc, length (compE2 a) + pc, xcp)"

| bisim1AAss3':
  "\<lbrakk> P, e, n, h \<turnstile>' (e', xs) \<leftrightarrow> (stk, loc, pc, xcp); bsok e n;
     \<And>xs. P, a, n, h \<turnstile>' (a, xs) \<leftrightarrow> ([], xs, 0, None); bsok a n;  
     \<And>xs. P, i, n, h \<turnstile>' (i, xs) \<leftrightarrow> ([], xs, 0, None); bsok i n \<rbrakk>
  \<Longrightarrow> P, a\<lfloor>i\<rceil> := e, n, h \<turnstile>' (Val v\<lfloor>Val v'\<rceil> := e', xs) \<leftrightarrow> (stk @ [v', v], loc, length (compE2 a) + length (compE2 i) + pc, xcp)"

| bisim1AAssThrow1':
  "\<lbrakk> P, a, n, h \<turnstile>' (Throw ad, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>ad\<rfloor>); bsok a n;
     \<And>xs. P, i, n, h \<turnstile>' (i, xs) \<leftrightarrow> ([], xs, 0, None); bsok i n; 
     \<And>xs. P, e, n, h \<turnstile>' (e, xs) \<leftrightarrow> ([], xs, 0, None); bsok e n \<rbrakk>
  \<Longrightarrow> P, a\<lfloor>i\<rceil> := e, n, h \<turnstile>' (Throw ad, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>ad\<rfloor>)"

| bisim1AAssThrow2':
  "\<lbrakk> P, i, n, h \<turnstile>' (Throw ad, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>ad\<rfloor>); bsok i n;
     \<And>xs. P, a, n, h \<turnstile>' (a, xs) \<leftrightarrow> ([], xs, 0, None); bsok a n; 
     \<And>xs. P, e, n, h \<turnstile>' (e, xs) \<leftrightarrow> ([], xs, 0, None); bsok e n \<rbrakk>
  \<Longrightarrow> P, a\<lfloor>i\<rceil> := e, n, h \<turnstile>' (Throw ad, xs) \<leftrightarrow> (stk @ [v], loc, length (compE2 a) + pc, \<lfloor>ad\<rfloor>)"

| bisim1AAssThrow3':
  "\<lbrakk> P, e, n, h \<turnstile>' (Throw ad, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>ad\<rfloor>); bsok e n;
     \<And>xs. P, a, n, h \<turnstile>' (a, xs) \<leftrightarrow> ([], xs, 0, None); bsok a n;  
     \<And>xs. P, i, n, h \<turnstile>' (i, xs) \<leftrightarrow> ([], xs, 0, None); bsok i n \<rbrakk>
  \<Longrightarrow> P, a\<lfloor>i\<rceil> := e, n, h \<turnstile>' (Throw ad, xs) \<leftrightarrow> (stk @ [v', v], loc, length (compE2 a) + length (compE2 i) + pc, \<lfloor>ad\<rfloor>)"

| bisim1AAssNull':
  "\<lbrakk> \<And>xs. P, a, n, h \<turnstile>' (a, xs) \<leftrightarrow> ([], xs, 0, None); bsok a n;  
     \<And>xs. P, i, n, h \<turnstile>' (i, xs) \<leftrightarrow> ([], xs, 0, None); bsok i n;
     \<And>xs. P, e, n, h \<turnstile>' (e, xs) \<leftrightarrow> ([], xs, 0, None); bsok e n \<rbrakk>
  \<Longrightarrow> P, a\<lfloor>i\<rceil> := e, n, h \<turnstile>' (THROW NullPointer, xs) \<leftrightarrow> ([v', v, Null], xs, length (compE2 a) + length (compE2 i) + length (compE2 e), \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>)"

| bisim1AAssBounds':
  "\<lbrakk> \<And>xs. P, a, n, h \<turnstile>' (a, xs) \<leftrightarrow> ([], xs, 0, None); bsok a n;  
     \<And>xs. P, i, n, h \<turnstile>' (i, xs) \<leftrightarrow> ([], xs, 0, None); bsok i n;
     \<And>xs. P, e, n, h \<turnstile>' (e, xs) \<leftrightarrow> ([], xs, 0, None); bsok e n \<rbrakk>
  \<Longrightarrow> P, a\<lfloor>i\<rceil> := e, n, h \<turnstile>' (THROW ArrayIndexOutOfBounds, xs) \<leftrightarrow> ([v', v, Addr a'], xs, length (compE2 a) + length (compE2 i) + length (compE2 e), \<lfloor>addr_of_sys_xcpt ArrayIndexOutOfBounds\<rfloor>)"

| bisim1AAssStore':
  "\<lbrakk> \<And>xs. P, a, n, h \<turnstile>' (a, xs) \<leftrightarrow> ([], xs, 0, None); bsok a n;  
     \<And>xs. P, i, n, h \<turnstile>' (i, xs) \<leftrightarrow> ([], xs, 0, None); bsok i n;
     \<And>xs. P, e, n, h \<turnstile>' (e, xs) \<leftrightarrow> ([], xs, 0, None); bsok e n \<rbrakk>
  \<Longrightarrow> P, a\<lfloor>i\<rceil> := e, n, h \<turnstile>' (THROW ArrayStore, xs) \<leftrightarrow> ([v', v, Addr a'], xs, length (compE2 a) + length (compE2 i) + length (compE2 e), \<lfloor>addr_of_sys_xcpt ArrayStore\<rfloor>)"

| bisim1AAss4':
  "\<lbrakk> \<And>xs. P, a, n, h \<turnstile>' (a, xs) \<leftrightarrow> ([], xs, 0, None); bsok a n;  
     \<And>xs. P, i, n, h \<turnstile>' (i, xs) \<leftrightarrow> ([], xs, 0, None); bsok i n;
     \<And>xs. P, e, n, h \<turnstile>' (e, xs) \<leftrightarrow> ([], xs, 0, None); bsok e n \<rbrakk>
  \<Longrightarrow> P, a\<lfloor>i\<rceil> := e, n, h \<turnstile>' (unit, xs) \<leftrightarrow> ([], xs, Suc (length (compE2 a) + length (compE2 i) + length (compE2 e)), None)"


| bisim1ALength': 
  "\<lbrakk> P, a, n, h \<turnstile>' (a', xs) \<leftrightarrow> (stk, loc, pc, xcp); bsok a n \<rbrakk>
  \<Longrightarrow> P, a\<bullet>length, n, h \<turnstile>' (a'\<bullet>length, xs) \<leftrightarrow> (stk, loc, pc, xcp)"

| bisim1ALengthThrow':
  "\<lbrakk> P, a, n, h \<turnstile>' (Throw ad, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>ad\<rfloor>); bsok a n \<rbrakk>
  \<Longrightarrow> P, a\<bullet>length, n, h \<turnstile>' (Throw ad, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>ad\<rfloor>)"


| bisim1ALengthNull':
  "\<lbrakk> \<And>xs. P, a, n, h \<turnstile>' (a, xs) \<leftrightarrow> ([], xs, 0, None); bsok a n \<rbrakk>
  \<Longrightarrow> P, a\<bullet>length, n, h \<turnstile>' (THROW NullPointer, xs) \<leftrightarrow> ([Null], xs, length (compE2 a), \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>)"


| bisim1FAcc': 
  "\<lbrakk> P, e, n, h \<turnstile>' (e', xs) \<leftrightarrow> (stk, loc, pc, xcp); bsok e n \<rbrakk>
  \<Longrightarrow> P, e\<bullet>F{D}, n, h \<turnstile>' (e'\<bullet>F{D}, xs) \<leftrightarrow> (stk, loc, pc, xcp)"

| bisim1FAccThrow':
  "\<lbrakk> P, e, n, h \<turnstile>' (Throw ad, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>ad\<rfloor>); bsok e n \<rbrakk>
  \<Longrightarrow> P, e\<bullet>F{D}, n, h \<turnstile>' (Throw ad, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>ad\<rfloor>)"

| bisim1FAccNull':
  "\<lbrakk> \<And>xs. P, e, n, h \<turnstile>' (e, xs) \<leftrightarrow> ([], xs, 0, None); bsok e n \<rbrakk>
   \<Longrightarrow> P, e\<bullet>F{D}, n, h \<turnstile>' (THROW NullPointer, xs) \<leftrightarrow> ([Null], xs, length (compE2 e), \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>)"


| bisim1FAss1': 
  "\<lbrakk> P, e, n, h \<turnstile>' (e', xs) \<leftrightarrow> (stk, loc, pc, xcp); bsok e n;  
     \<And>xs. P, e2, n, h \<turnstile>' (e2, xs) \<leftrightarrow> ([], xs, 0, None); bsok e2 n \<rbrakk>
  \<Longrightarrow> P, e\<bullet>F{D} := e2, n, h \<turnstile>' (e'\<bullet>F{D} := e2, xs) \<leftrightarrow> (stk, loc, pc, xcp)"

| bisim1FAss2': 
  "\<lbrakk> P, e2, n, h \<turnstile>' (e', xs) \<leftrightarrow> (stk, loc, pc, xcp); bsok e2 n;  
     \<And>xs. P, e, n, h \<turnstile>' (e, xs) \<leftrightarrow> ([], xs, 0, None); bsok e n \<rbrakk>
  \<Longrightarrow> P, e\<bullet>F{D} := e2, n, h \<turnstile>' (Val v\<bullet>F{D} := e', xs) \<leftrightarrow> (stk @ [v], loc, length (compE2 e) + pc, xcp)"

| bisim1FAssThrow1':
  "\<lbrakk> P, e, n, h \<turnstile>' (Throw ad, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>ad\<rfloor>); bsok e n;  
     \<And>xs. P, e2, n, h \<turnstile>' (e2, xs) \<leftrightarrow> ([], xs, 0, None); bsok e2 n \<rbrakk>
  \<Longrightarrow> P, e\<bullet>F{D} := e2, n, h \<turnstile>' (Throw ad, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>ad\<rfloor>)"

| bisim1FAssThrow2':
  "\<lbrakk> P, e2, n, h \<turnstile>' (Throw ad, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>ad\<rfloor>); bsok e2 n;  
     \<And>xs. P, e, n, h \<turnstile>' (e, xs) \<leftrightarrow> ([], xs, 0, None); bsok e n \<rbrakk>
  \<Longrightarrow> P, e\<bullet>F{D} := e2, n, h \<turnstile>' (Throw ad, xs) \<leftrightarrow> (stk @ [v], loc, length (compE2 e) + pc, \<lfloor>ad\<rfloor>)"

| bisim1FAssNull':
  "\<lbrakk> \<And>xs. P, e, n, h \<turnstile>' (e, xs) \<leftrightarrow> ([], xs, 0, None); bsok e n;
     \<And>xs. P, e2, n, h \<turnstile>' (e2, xs) \<leftrightarrow> ([], xs, 0, None);  bsok e2 n \<rbrakk>
   \<Longrightarrow> P, e\<bullet>F{D} := e2, n, h \<turnstile>' (THROW NullPointer, xs) \<leftrightarrow> ([v, Null], xs, length (compE2 e) + length (compE2 e2), \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>)"

| bisim1FAss3':
  "\<lbrakk> \<And>xs. P, e, n, h \<turnstile>' (e, xs) \<leftrightarrow> ([], xs, 0, None); bsok e n;
     \<And>xs. P, e2, n, h \<turnstile>' (e2, xs) \<leftrightarrow> ([], xs, 0, None);  bsok e2 n \<rbrakk>
   \<Longrightarrow> P, e\<bullet>F{D} := e2, n, h \<turnstile>' (unit, xs) \<leftrightarrow> ([], xs, Suc (length (compE2 e) + length (compE2 e2)), None)"


| bisim1Call1':
  "\<lbrakk> P, obj, n, h \<turnstile>' (obj', xs) \<leftrightarrow> (stk, loc, pc, xcp);
     bsok obj n; bsoks ps n; \<And>xs. P, ps, n, h \<turnstile>' (ps, xs) [\<leftrightarrow>] ([], xs, 0, None) \<rbrakk>
  \<Longrightarrow> P, obj\<bullet>M(ps), n, h \<turnstile>' (obj'\<bullet>M(ps), xs) \<leftrightarrow> (stk, loc, pc, xcp)"

| bisim1CallParams':
  "\<lbrakk> P, ps, n, h \<turnstile>' (ps', xs) [\<leftrightarrow>] (stk, loc, pc, xcp); ps \<noteq> [];
     bsok obj n; bsoks ps n; \<And>xs. P, obj, n, h \<turnstile>' (obj, xs) \<leftrightarrow> ([], xs, 0, None) \<rbrakk>
  \<Longrightarrow> P, obj\<bullet>M(ps), n, h \<turnstile>' (Val v\<bullet>M(ps'), xs) \<leftrightarrow> (stk @ [v], loc, length (compE2 obj) +  pc, xcp)"

| bisim1CallThrowObj':
  "\<lbrakk> P, obj, n, h \<turnstile>' (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>);
     bsok obj n; bsoks ps n; \<And>xs. P, ps, n, h \<turnstile>' (ps, xs) [\<leftrightarrow>] ([], xs, 0, None)\<rbrakk>
  \<Longrightarrow> P, obj\<bullet>M(ps), n, h \<turnstile>' (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)"

| bisim1CallThrowParams':
  "\<lbrakk> P, ps, n, h \<turnstile>' (map Val vs @ Throw a # ps', xs) [\<leftrightarrow>] (stk, loc, pc, \<lfloor>a\<rfloor>);
     bsoks ps n; bsok obj n; \<And>xs. P, obj, n, h \<turnstile>' (obj, xs) \<leftrightarrow> ([], xs, 0, None) \<rbrakk>
  \<Longrightarrow> P, obj\<bullet>M(ps), n, h \<turnstile>' (Throw a, xs) \<leftrightarrow> (stk @ [v], loc, length (compE2 obj) + pc, \<lfloor>a\<rfloor>)"

| bisim1CallThrow':
  "\<lbrakk> length ps = length vs; bsok obj n; bsoks ps n;
     \<And>xs. P, obj, n, h \<turnstile>' (obj, xs) \<leftrightarrow> ([], xs, 0, None); \<And>xs. P, ps, n, h \<turnstile>' (ps, xs) [\<leftrightarrow>] ([], xs, 0, None) \<rbrakk>
  \<Longrightarrow> P, obj\<bullet>M(ps), n, h \<turnstile>' (Throw a, xs) \<leftrightarrow> (vs @ [v], xs, length (compE2 obj) + length (compEs2 ps), \<lfloor>a\<rfloor>)"

| bisim1BlockSome1':
  "\<lbrakk> bsok e (Suc V); \<And>xs. P, e, Suc V, h \<turnstile>' (e, xs) \<leftrightarrow> ([], xs, 0, None) \<rbrakk>
  \<Longrightarrow> P, {V:T=\<lfloor>v\<rfloor>; e}\<^bsub>False\<^esub>, V, h \<turnstile>' ({V:T=\<lfloor>v\<rfloor>; e}\<^bsub>False\<^esub>, xs) \<leftrightarrow> ([], xs, 0, None)"

| bisim1BlockSome2':
  "\<lbrakk> bsok e (Suc V);  \<And>xs. P, e, Suc V, h \<turnstile>' (e, xs) \<leftrightarrow> ([], xs, 0, None) \<rbrakk>
  \<Longrightarrow> P, {V:T=\<lfloor>v\<rfloor>; e}\<^bsub>False\<^esub>, V, h \<turnstile>' ({V:T=\<lfloor>v\<rfloor>; e}\<^bsub>False\<^esub>, xs) \<leftrightarrow> ([v], xs, Suc 0, None)"

| bisim1BlockSome3':
  "\<lbrakk> P,e,Suc V,h \<turnstile>' (e',xs[V := v]) \<leftrightarrow> (stk, loc, pc, xcp); bsok e (Suc V) \<rbrakk>
  \<Longrightarrow> P, {V:T=\<lfloor>v\<rfloor>; e}\<^bsub>False\<^esub>, V, h \<turnstile>' ({V:T=\<lfloor>v\<rfloor>; e'}\<^bsub>False\<^esub>, xs) \<leftrightarrow> (stk, loc, Suc (Suc pc), xcp)"

| bisim1BlockSome4':
  "\<lbrakk> P, e, Suc V, h \<turnstile>' (e', xs) \<leftrightarrow> (stk, loc, pc, xcp); bsok e (Suc V) \<rbrakk>
  \<Longrightarrow> P, {V:T=\<lfloor>v\<rfloor>; e}\<^bsub>False\<^esub>, V, h \<turnstile>' ({V:T=None; e'}\<^bsub>False\<^esub>, xs) \<leftrightarrow> (stk, loc, Suc (Suc pc), xcp)"

| bisim1BlockThrowSome':
  "\<lbrakk> P, e, Suc V, h \<turnstile>' (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>); bsok e (Suc V) \<rbrakk>
  \<Longrightarrow> P, {V:T=\<lfloor>v\<rfloor>; e}\<^bsub>False\<^esub>, V, h \<turnstile>' (Throw a, xs) \<leftrightarrow> (stk, loc, Suc (Suc pc), \<lfloor>a\<rfloor>)"

| bisim1BlockNone':
  "\<lbrakk> P, e, Suc V, h \<turnstile>' (e', xs) \<leftrightarrow> (stk, loc, pc, xcp); bsok e (Suc V) \<rbrakk>
  \<Longrightarrow> P, {V:T=None; e}\<^bsub>False\<^esub>, V, h \<turnstile>' ({V:T=None; e'}\<^bsub>False\<^esub>, xs) \<leftrightarrow> (stk, loc, pc, xcp)"

| bisim1BlockThrowNone':
  "\<lbrakk> P, e, Suc V, h \<turnstile>' (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>); bsok e (Suc V) \<rbrakk>
  \<Longrightarrow> P, {V:T=None; e}\<^bsub>False\<^esub>, V, h \<turnstile>' (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)"


| bisim1Sync1':
  "\<lbrakk> P, e1, V, h \<turnstile>' (e', xs) \<leftrightarrow> (stk, loc, pc, xcp); bsok e1 V; bsok e2 (Suc V);
     \<And>xs. P, e2, Suc V, h \<turnstile>' (e2, xs) \<leftrightarrow> ([], xs, 0, None) \<rbrakk>
  \<Longrightarrow> P, sync\<^bsub>V\<^esub> (e1) e2, V, h \<turnstile>' (sync\<^bsub>V\<^esub> (e') e2, xs) \<leftrightarrow> (stk, loc, pc, xcp)"

| bisim1Sync2':
  "\<lbrakk> bsok e1 V; bsok e2 (Suc V); \<And>xs. P, e1, V, h \<turnstile>' (e1, xs) \<leftrightarrow> ([], xs, 0, None);
    \<And>xs. P, e2, Suc V, h \<turnstile>' (e2, xs) \<leftrightarrow> ([], xs, 0, None) \<rbrakk>
  \<Longrightarrow> P, sync\<^bsub>V\<^esub> (e1) e2, V, h \<turnstile>' (sync\<^bsub>V\<^esub> (Val v) e2, xs) \<leftrightarrow> ([], xs[V := v], Suc (length (compE2 e1)), None)"

| bisim1Sync3':
  "\<lbrakk> bsok e1 V; bsok e2 (Suc V); \<And>xs. P, e1, V, h \<turnstile>' (e1, xs) \<leftrightarrow> ([], xs, 0, None);
    \<And>xs. P, e2, Suc V, h \<turnstile>' (e2, xs) \<leftrightarrow> ([], xs, 0, None) \<rbrakk>
  \<Longrightarrow> P, sync\<^bsub>V\<^esub> (e1) e2, V, h \<turnstile>' (sync\<^bsub>V\<^esub> (Val v) e2, xs) \<leftrightarrow> ([v], xs[V := v], Suc (Suc (length (compE2 e1))), None)"

| bisim1Sync4':
  "\<lbrakk> P, e2, Suc V, h \<turnstile>' (e', xs) \<leftrightarrow> (stk, loc, pc, xcp); bsok e1 V;
     bsok e2 (Suc V); \<And>xs. P, e1, V, h \<turnstile>' (e1, xs) \<leftrightarrow> ([], xs, 0, None) \<rbrakk>
  \<Longrightarrow> P, sync\<^bsub>V\<^esub> (e1) e2, V, h \<turnstile>' (insync\<^bsub>V\<^esub> (a) e', xs) \<leftrightarrow> (stk, loc, Suc (Suc (Suc (length (compE2 e1) + pc))), xcp)"

| bisim1Sync5':
  "\<lbrakk> bsok e1 V; bsok e2 (Suc V); \<And>xs. P, e1, V, h \<turnstile>' (e1, xs) \<leftrightarrow> ([], xs, 0, None);
    \<And>xs. P, e2, Suc V, h \<turnstile>' (e2, xs) \<leftrightarrow> ([], xs, 0, None) \<rbrakk>
  \<Longrightarrow> P, sync\<^bsub>V\<^esub> (e1) e2, V, h \<turnstile>' (insync\<^bsub>V\<^esub> (a) Val v, xs) \<leftrightarrow> ([xs ! V, v], xs, 4 + length (compE2 e1) + length (compE2 e2), None)"

| bisim1Sync6':
  "\<lbrakk> bsok e1 V; bsok e2 (Suc V); \<And>xs. P, e1, V, h \<turnstile>' (e1, xs) \<leftrightarrow> ([], xs, 0, None);
    \<And>xs. P, e2, Suc V, h \<turnstile>' (e2, xs) \<leftrightarrow> ([], xs, 0, None) \<rbrakk>
  \<Longrightarrow> P, sync\<^bsub>V\<^esub> (e1) e2, V, h \<turnstile>' (Val v, xs) \<leftrightarrow> ([v], xs, 5 + length (compE2 e1) + length (compE2 e2), None)"

| bisim1Sync7':
  "\<lbrakk> bsok e1 V; bsok e2 (Suc V); \<And>xs. P, e1, V, h \<turnstile>' (e1, xs) \<leftrightarrow> ([], xs, 0, None);
    \<And>xs. P, e2, Suc V, h \<turnstile>' (e2, xs) \<leftrightarrow> ([], xs, 0, None) \<rbrakk>
  \<Longrightarrow> P, sync\<^bsub>V\<^esub> (e1) e2, V, h \<turnstile>' (insync\<^bsub>V\<^esub> (a) Throw a', xs) \<leftrightarrow> ([Addr a'], xs, 6 + length (compE2 e1) + length (compE2 e2), None)"

| bisim1Sync8':
  "\<lbrakk> bsok e1 V; bsok e2 (Suc V); \<And>xs. P, e1, V, h \<turnstile>' (e1, xs) \<leftrightarrow> ([], xs, 0, None);
    \<And>xs. P, e2, Suc V, h \<turnstile>' (e2, xs) \<leftrightarrow> ([], xs, 0, None) \<rbrakk>
  \<Longrightarrow> P, sync\<^bsub>V\<^esub> (e1) e2, V, h \<turnstile>' (insync\<^bsub>V\<^esub> (a) Throw a', xs) \<leftrightarrow>
        ([xs ! V, Addr a'], xs, 7 + length (compE2 e1) + length (compE2 e2), None)"

| bisim1Sync9':
  "\<lbrakk> bsok e1 V; bsok e2 (Suc V); \<And>xs. P, e1, V, h \<turnstile>' (e1, xs) \<leftrightarrow> ([], xs, 0, None);
    \<And>xs. P, e2, Suc V, h \<turnstile>' (e2, xs) \<leftrightarrow> ([], xs, 0, None) \<rbrakk>
  \<Longrightarrow> P, sync\<^bsub>V\<^esub> (e1) e2, V, h \<turnstile>' (Throw a, xs) \<leftrightarrow> ([Addr a], xs, 8 + length (compE2 e1) + length (compE2 e2), None)"

| bisim1Sync10':
  "\<lbrakk> bsok e1 V; bsok e2 (Suc V); \<And>xs. P, e1, V, h \<turnstile>' (e1, xs) \<leftrightarrow> ([], xs, 0, None);
    \<And>xs. P, e2, Suc V, h \<turnstile>' (e2, xs) \<leftrightarrow> ([], xs, 0, None) \<rbrakk>
  \<Longrightarrow> P, sync\<^bsub>V\<^esub> (e1) e2, V, h \<turnstile>' (Throw a, xs) \<leftrightarrow> ([Addr a], xs, 8 + length (compE2 e1) + length (compE2 e2), \<lfloor>a\<rfloor>)"

| bisim1Sync11':
  "\<lbrakk> bsok e1 V; bsok e2 (Suc V); \<And>xs. P, e1, V, h \<turnstile>' (e1, xs) \<leftrightarrow> ([], xs, 0, None);
    \<And>xs. P, e2, Suc V, h \<turnstile>' (e2, xs) \<leftrightarrow> ([], xs, 0, None) \<rbrakk>
  \<Longrightarrow> P, sync\<^bsub>V\<^esub> (e1) e2, V, h \<turnstile>' (THROW NullPointer, xs) \<leftrightarrow> ([Null], xs, Suc (Suc (length (compE2 e1))), \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>)"

| bisim1Sync12':
  "\<lbrakk> bsok e1 V; bsok e2 (Suc V); \<And>xs. P, e1, V, h \<turnstile>' (e1, xs) \<leftrightarrow> ([], xs, 0, None);
    \<And>xs. P, e2, Suc V, h \<turnstile>' (e2, xs) \<leftrightarrow> ([], xs, 0, None) \<rbrakk>
  \<Longrightarrow> P, sync\<^bsub>V\<^esub> (e1) e2, V, h \<turnstile>' (THROW NullPointer, xs) \<leftrightarrow> ([Null, v], xs, 4 + length (compE2 e1) + length (compE2 e2), \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>)"

| bisim1Sync13':
  "\<lbrakk> bsok e1 V; bsok e2 (Suc V); \<And>xs. P, e1, V, h \<turnstile>' (e1, xs) \<leftrightarrow> ([], xs, 0, None);
    \<And>xs. P, e2, Suc V, h \<turnstile>' (e2, xs) \<leftrightarrow> ([], xs, 0, None) \<rbrakk>
  \<Longrightarrow> P, sync\<^bsub>V\<^esub> (e1) e2, V, h \<turnstile>' (THROW IllegalMonitorState, xs) \<leftrightarrow> ([v', v], xs, 4 + length (compE2 e1) + length (compE2 e2), \<lfloor>addr_of_sys_xcpt IllegalMonitorState\<rfloor>)"

| bisim1Sync14':
  "\<lbrakk> bsok e1 V; bsok e2 (Suc V); \<And>xs. P, e1, V, h \<turnstile>' (e1, xs) \<leftrightarrow> ([], xs, 0, None);
    \<And>xs. P, e2, Suc V, h \<turnstile>' (e2, xs) \<leftrightarrow> ([], xs, 0, None) \<rbrakk>
  \<Longrightarrow> P, sync\<^bsub>V\<^esub> (e1) e2, V, h \<turnstile>' (THROW IllegalMonitorState, xs) \<leftrightarrow>
        ([v, Addr a'], xs, 7 + length (compE2 e1) + length (compE2 e2), \<lfloor>addr_of_sys_xcpt IllegalMonitorState\<rfloor>)"

| bisim1Sync15':
  "\<lbrakk> bsok e1 V; bsok e2 (Suc V); \<And>xs. P, e1, V, h \<turnstile>' (e1, xs) \<leftrightarrow> ([], xs, 0, None);
    \<And>xs. P, e2, Suc V, h \<turnstile>' (e2, xs) \<leftrightarrow> ([], xs, 0, None) \<rbrakk>
  \<Longrightarrow> P, sync\<^bsub>V\<^esub> (e1) e2, V, h \<turnstile>' (THROW NullPointer, xs) \<leftrightarrow>
        ([Null, Addr a'], xs, 7 + length (compE2 e1) + length (compE2 e2), \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>)"


| bisim1SyncThrow':
  "\<lbrakk> P, e1, V, h \<turnstile>' (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>); bsok e2 (Suc V); bsok e1 V;
    \<And>xs. P, e2, Suc V, h \<turnstile>' (e2, xs) \<leftrightarrow> ([], xs, 0, None) \<rbrakk>
  \<Longrightarrow> P, sync\<^bsub>V\<^esub> (e1) e2, V, h \<turnstile>' (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)"


| bisim1Seq1':
  "\<lbrakk> P, e1, n, h \<turnstile>' (e', xs) \<leftrightarrow> (stk, loc, pc, xcp); bsok e1 n;
     bsok e2 n; \<And>xs. P, e2, n, h \<turnstile>' (e2, xs) \<leftrightarrow> ([], xs, 0, None) \<rbrakk>
   \<Longrightarrow> P, e1;;e2, n, h \<turnstile>' (e';;e2, xs) \<leftrightarrow> (stk, loc, pc, xcp)"

| bisim1SeqThrow1':
  "\<lbrakk> P, e1, n, h \<turnstile>' (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>); bsok e1 n;
     bsok e2 n; \<And>xs. P, e2, n, h \<turnstile>' (e2, xs) \<leftrightarrow> ([], xs, 0, None) \<rbrakk>
   \<Longrightarrow> P, e1;;e2, n, h \<turnstile>' (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)"

| bisim1Seq2':
  "\<lbrakk> P, e2, n, h \<turnstile>' (e', xs) \<leftrightarrow> (stk, loc, pc, xcp); bsok e1 n;
     bsok e2 n; \<And>xs. P, e1, n, h \<turnstile>' (e1, xs) \<leftrightarrow> ([], xs, 0, None) \<rbrakk>
  \<Longrightarrow> P, e1;;e2, n, h \<turnstile>' (e', xs) \<leftrightarrow> (stk, loc, Suc (length (compE2 e1) + pc), xcp)"


| bisim1Cond1':
  "\<lbrakk> P, e, n, h \<turnstile>' (e', xs) \<leftrightarrow> (stk, loc, pc, xcp); bsok e n;
     bsok e1 n; bsok e2 n; \<And>xs. P, e1, n, h \<turnstile>' (e1, xs) \<leftrightarrow> ([], xs, 0, None);
     \<And>xs. P, e2, n, h \<turnstile>' (e2, xs) \<leftrightarrow> ([], xs, 0, None) \<rbrakk>
  \<Longrightarrow> P, if (e) e1 else e2, n, h \<turnstile>' (if (e') e1 else e2, xs) \<leftrightarrow> (stk, loc, pc, xcp)"

| bisim1CondThen':
  "\<lbrakk> P, e1, n, h \<turnstile>' (e', xs) \<leftrightarrow> (stk, loc, pc, xcp); bsok e n;
     bsok e1 n; bsok e2 n; \<And>xs. P, e, n, h \<turnstile>' (e, xs) \<leftrightarrow> ([], xs, 0, None);
     \<And>xs. P, e2, n, h \<turnstile>' (e2, xs) \<leftrightarrow> ([], xs, 0, None) \<rbrakk>
  \<Longrightarrow> P, if (e) e1 else e2, n, h \<turnstile>' (e', xs) \<leftrightarrow> (stk, loc, Suc (length (compE2 e) + pc), xcp)"

| bisim1CondElse':
  "\<lbrakk> P, e2, n, h \<turnstile>' (e', xs) \<leftrightarrow> (stk, loc, pc, xcp); bsok e n;
     bsok e1 n; bsok e2 n; \<And>xs. P, e, n, h \<turnstile>' (e, xs) \<leftrightarrow> ([], xs, 0, None);
     \<And>xs. P, e1, n, h \<turnstile>' (e1, xs) \<leftrightarrow> ([], xs, 0, None) \<rbrakk>
  \<Longrightarrow> P, if (e) e1 else e2, n, h \<turnstile>' (e', xs) \<leftrightarrow> (stk, loc, Suc (Suc (length (compE2 e) + length (compE2 e1) +  pc)), xcp)"

| bisim1CondThrow':
  "\<lbrakk> P, e, n, h \<turnstile>' (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>); bsok e n;
     bsok e1 n; bsok e2 n; \<And>xs. P, e1, n, h \<turnstile>' (e1, xs) \<leftrightarrow> ([], xs, 0, None);
     \<And>xs. P, e2, n, h \<turnstile>' (e2, xs) \<leftrightarrow> ([], xs, 0, None) \<rbrakk>
  \<Longrightarrow> P, if (e) e1 else e2, n, h \<turnstile>' (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)"


| bisim1While1':
  "\<lbrakk> bsok c n; bsok e n; \<And>xs. P, c, n, h \<turnstile>' (c, xs) \<leftrightarrow> ([], xs, 0, None);
     \<And>xs. P, e, n, h \<turnstile>' (e, xs) \<leftrightarrow> ([], xs, 0, None) \<rbrakk>
  \<Longrightarrow> P, while (c) e, n, h \<turnstile>' (while (c) e, xs) \<leftrightarrow> ([], xs, 0, None)"

| bisim1While3':
  "\<lbrakk> P, c, n, h \<turnstile>' (e', xs) \<leftrightarrow> (stk, loc, pc, xcp); bsok e n; bsok c n;
     \<And>xs. P, e, n, h \<turnstile>' (e, xs) \<leftrightarrow> ([], xs, 0, None) \<rbrakk>
  \<Longrightarrow> P, while (c) e, n, h \<turnstile>' (if (e') (e;; while (c) e) else unit, xs) \<leftrightarrow> (stk, loc, pc, xcp)"

| bisim1While4':
  "\<lbrakk> P, e, n, h \<turnstile>' (e', xs) \<leftrightarrow> (stk, loc, pc, xcp); bsok c n;
     bsok e n; \<And>xs. P, c, n, h \<turnstile>' (c, xs) \<leftrightarrow> ([], xs, 0, None) \<rbrakk>
  \<Longrightarrow> P, while (c) e, n, h  \<turnstile>' (e';; while (c) e, xs) \<leftrightarrow> (stk, loc, Suc (length (compE2 c) + pc), xcp)"

| bisim1While6':
  "\<lbrakk> bsok c n; bsok e n; \<And>xs. P, c, n, h \<turnstile>' (c, xs) \<leftrightarrow> ([], xs, 0, None);
     \<And>xs. P, e, n, h \<turnstile>' (e, xs) \<leftrightarrow> ([], xs, 0, None) \<rbrakk> \<Longrightarrow> 
  P, while (c) e, n, h \<turnstile>' (while (c) e, xs) \<leftrightarrow> ([], xs, Suc (Suc (length (compE2 c) + length (compE2 e))), None)"

| bisim1While7':
  "\<lbrakk> bsok c n; bsok e n; \<And>xs. P, c, n, h \<turnstile>' (c, xs) \<leftrightarrow> ([], xs, 0, None);
     \<And>xs. P, e, n, h \<turnstile>' (e, xs) \<leftrightarrow> ([], xs, 0, None) \<rbrakk> \<Longrightarrow> 
  P, while (c) e, n, h \<turnstile>' (unit, xs) \<leftrightarrow> ([], xs, Suc (Suc (Suc (length (compE2 c) + length (compE2 e)))), None)"

| bisim1WhileThrow1':
  "\<lbrakk> P, c, n, h \<turnstile>' (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>); bsok e n; bsok c n;
     \<And>xs. P, e, n, h \<turnstile>' (e, xs) \<leftrightarrow> ([], xs, 0, None) \<rbrakk>
  \<Longrightarrow> P, while (c) e, n, h \<turnstile>' (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)"

| bisim1WhileThrow2':
  "\<lbrakk> P, e, n, h \<turnstile>' (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>); bsok c n;
     bsok e n; \<And>xs. P, c, n, h \<turnstile>' (c, xs) \<leftrightarrow> ([], xs, 0, None) \<rbrakk>
   \<Longrightarrow> P, while (c) e, n, h \<turnstile>' (Throw a, xs) \<leftrightarrow> (stk, loc, Suc (length (compE2 c) + pc), \<lfloor>a\<rfloor>)"


| bisim1Throw1':
  "\<lbrakk> P, e, n, h \<turnstile>' (e', xs) \<leftrightarrow> (stk, loc, pc, xcp); bsok e n \<rbrakk>
  \<Longrightarrow> P, throw e, n, h \<turnstile>' (throw e', xs) \<leftrightarrow> (stk, loc, pc, xcp)"

| bisim1Throw2':
  "\<lbrakk> bsok e n; \<And>xs. P, e, n, h \<turnstile>' (e, xs) \<leftrightarrow> ([], xs, 0, None) \<rbrakk>
  \<Longrightarrow> P, throw e, n, h \<turnstile>' (Throw a, xs) \<leftrightarrow> ([Addr a], xs, length (compE2 e), \<lfloor>a\<rfloor>)"

| bisim1ThrowNull':
  "\<lbrakk> bsok e n; \<And>xs. P, e, n, h \<turnstile>' (e, xs) \<leftrightarrow> ([], xs, 0, None) \<rbrakk>
  \<Longrightarrow> P, throw e, n, h \<turnstile>' (THROW NullPointer, xs) \<leftrightarrow> ([Null], xs, length (compE2 e), \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>)"

| bisim1ThrowThrow':
  "\<lbrakk> P, e, n, h \<turnstile>' (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>); bsok e n \<rbrakk>
  \<Longrightarrow> P, throw e, n, h \<turnstile>' (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)"


| bisim1Try':
  "\<lbrakk> P, e, V, h \<turnstile>' (e', xs) \<leftrightarrow> (stk, loc, pc, xcp); bsok e V;
     bsok e2 (Suc V); \<And>xs. P, e2, Suc V, h \<turnstile>' (e2, xs) \<leftrightarrow> ([], xs, 0, None) \<rbrakk>
   \<Longrightarrow> P, try e catch(C V) e2, V, h \<turnstile>' (try e' catch(C V) e2, xs) \<leftrightarrow> (stk, loc, pc, xcp)"

| bisim1TryCatch1':
  "\<lbrakk> P, e, V, h \<turnstile>' (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>); h a = \<lfloor>Obj C' fs\<rfloor>; P \<turnstile> C' \<preceq>\<^sup>* C;
     bsok e2 (Suc V); bsok e V; \<And>xs. P, e2, Suc V, h \<turnstile>' (e2, xs) \<leftrightarrow> ([], xs, 0, None) \<rbrakk>
  \<Longrightarrow> P, try e catch(C V) e2, V, h \<turnstile>' ({V:Class C=None; e2}\<^bsub>False\<^esub>, xs[V := Addr a]) \<leftrightarrow> ([Addr a], loc, Suc (length (compE2 e)), None)"

| bisim1TryCatch2':
  "\<lbrakk> P, e2, Suc V, h \<turnstile>' (e', xs) \<leftrightarrow> (stk, loc, pc, xcp); bsok e V;
    bsok e2 (Suc V); \<And>xs. P, e, V, h \<turnstile>' (e, xs) \<leftrightarrow> ([], xs, 0, None)\<rbrakk>
   \<Longrightarrow> P, try e catch(C V) e2, V, h \<turnstile>' ({V:Class C=None; e'}\<^bsub>False\<^esub>, xs) \<leftrightarrow> (stk, loc, Suc (Suc (length (compE2 e) + pc)), xcp)"

| bisim1TryFail':
  "\<lbrakk> P, e, V, h \<turnstile>' (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>); h a = \<lfloor>Obj C' fs\<rfloor>; \<not> P \<turnstile> C' \<preceq>\<^sup>* C;
     bsok e2 (Suc V); bsok e V; \<And>xs. P, e2, Suc V, h \<turnstile>' (e2, xs) \<leftrightarrow> ([], xs, 0, None) \<rbrakk> 
  \<Longrightarrow> P, try e catch(C V) e2, V, h \<turnstile>' (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)"

| bisim1TryCatchThrow':
  "\<lbrakk> P, e2, Suc V, h \<turnstile>' (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>); bsok e V;
     bsok e2 (Suc V); \<And>xs. P, e, V, h \<turnstile>' (e, xs) \<leftrightarrow> ([], xs, 0, None) \<rbrakk>
   \<Longrightarrow> P, try e catch(C V) e2, V, h \<turnstile>' (Throw a, xs) \<leftrightarrow> (stk, loc, Suc (Suc (length (compE2 e) + pc)), \<lfloor>a\<rfloor>)"

| bisims1Nil': "P, [], n, h \<turnstile>' ([], xs) [\<leftrightarrow>] ([], xs, 0, None)"

| bisims1List1':
  "\<lbrakk> P, e, n, h \<turnstile>' (e', xs) \<leftrightarrow> (stk, loc, pc, xcp); bsok e n;
     bsoks es n; \<And>xs. P, es, n, h \<turnstile>' (es, xs) [\<leftrightarrow>] ([], xs, 0, None) \<rbrakk>
  \<Longrightarrow> P, e#es, n, h \<turnstile>' (e'#es, xs) [\<leftrightarrow>] (stk, loc, pc, xcp)"

| bisims1List2':
  "\<lbrakk> P, es, n, h \<turnstile>' (es', xs) [\<leftrightarrow>] (stk, loc, pc, xcp); bsoks es n; 
     bsok e n; \<And>xs. P, e, n, h \<turnstile>' (e, xs) \<leftrightarrow> ([], xs, 0, None) \<rbrakk>
  \<Longrightarrow> P, e#es, n, h \<turnstile>' (Val v # es', xs) [\<leftrightarrow>] (stk @ [v], loc, length (compE2 e) + pc, xcp)"


lemma bisim1'_refl: "bsok e n \<Longrightarrow> P,e,n,h \<turnstile>' (e,xs) \<leftrightarrow> ([],xs,0,None)"
  and bisims1'_refl: "bsoks es n \<Longrightarrow> P,es,n,h \<turnstile>' (es,xs) [\<leftrightarrow>] ([],xs,0,None)"
apply(induct e and es arbitrary: n xs and n xs)
apply(auto intro: bisim1'_bisims1'.intros simp add: nat_fun_sum_eq_conv)
apply(case_tac option)
apply(auto intro: bisim1'_bisims1'.intros simp add: expand_fun_eq split: split_if_asm)
done


lemma bisim1_imp_bisim1': "P, e, n, h \<turnstile> exs \<leftrightarrow> s \<Longrightarrow> P, e, n, h \<turnstile>' exs \<leftrightarrow> s"
  and bisims1_imp_bisims1': "P, es, n, h \<turnstile> esxs [\<leftrightarrow>] s \<Longrightarrow> P, es, n, h \<turnstile>' esxs [\<leftrightarrow>] s"
proof(induct rule: bisim1_bisims1.inducts)
  case (bisim1CallParams ps n ps' xs stk loc pc xcp obj M v)
  show ?case
  proof(cases "ps = []")
    case True
    with `P,ps,n,h \<turnstile> (ps', xs) [\<leftrightarrow>] (stk, loc, pc, xcp)` have "ps' = []" "pc = 0" "stk = []" "loc = xs" "xcp = None"
      by(auto elim: bisims1.cases)
    moreover from `bsok obj n` have "P,obj,n,h \<turnstile>' (Val v,xs) \<leftrightarrow> ([v],xs,length (compE2 obj),None)"
      by(blast intro: bisim1Val2' bisim1'_refl)
    with `bsok obj n` have "P,obj\<bullet>M([]),n,h \<turnstile>' (Val v\<bullet>M([]),xs) \<leftrightarrow> ([v],xs,length (compE2 obj),None)"
      by-(rule bisim1Call1', auto intro!: bisims1Nil' simp add: bsoks_def)
    ultimately show ?thesis using True by simp
  next
    case False with bisim1CallParams show ?thesis
      by(auto intro: bisim1CallParams' bisims1'_refl bisims1_bsoks bisim1'_refl)
  qed
qed(auto intro: bisim1'_bisims1'.intros bisim1'_refl bisims1'_refl bisim1_bsok bisims1_bsoks)

lemma bisim1'_imp_bisim1: "P, e, n, h \<turnstile>' exs \<leftrightarrow> s \<Longrightarrow> P, e, n, h \<turnstile> exs \<leftrightarrow> s"
  and bisims1'_imp_bisims1: "P, es, n, h \<turnstile>' esxs [\<leftrightarrow>] s \<Longrightarrow> P, es, n, h \<turnstile> esxs [\<leftrightarrow>] s"
apply(induct rule: bisim1'_bisims1'.inducts)
apply(blast intro: bisim1_bisims1.intros)+
done

lemma bisim1'_eq_bisim1: "bisim1' = bisim1"
  and bisims1'_eq_bisims1: "bisims1' = bisims1"
by(blast intro!: ext bisim1_imp_bisim1' bisims1_imp_bisims1' bisim1'_imp_bisim1 bisims1'_imp_bisims1)+

lemmas bisim1_bisims1_inducts = bisim1'_bisims1'.inducts[unfolded bisim1'_eq_bisim1 bisims1'_eq_bisims1, consumes 1,
  case_names bisim1Val2 bisim1New bisim1NewThrow
  bisim1NewArray bisim1NewArrayThrow bisim1NewArrayNegative bisim1NewArrayFail bisim1Cast bisim1CastThrow bisim1CastFail
  bisim1Val bisim1Var bisim1BinOp1 bisim1BinOp2 bisim1BinOpThrow1 bisim1BinOpThrow2
  bisim1LAss1 bisim1LAss2 bisim1LAssThrow
  bisim1AAcc1 bisim1AAcc2 bisim1AAccThrow1 bisim1AAccThrow2 bisim1AAccNull bisim1AAccBounds
  bisim1AAss1 bisim1AAss2 bisim1AAss3 bisim1AAssThrow1 bisim1AAssThrow2
  bisim1AAssThrow3 bisim1AAssNull bisim1AAssBounds bisim1AAssStore bisim1AAss4
  bisim1ALength bisim1ALengthThrow bisim1ALengthNull
  bisim1FAcc bisim1FAccThrow bisim1FAccNull
  bisim1FAss1 bisim1FAss2 bisim1FAssThrow1 bisim1FAssThrow2 bisim1FAssNull bisim1FAss3
  bisim1Call1 bisim1CallParams bisim1CallThrowObj bisim1CallThrowParams
  bisim1CallThrow
  bisim1BlockSome1 bisim1BlockSome2 bisim1BlockSome3 bisim1BlockSome4 bisim1BlockThrowSome
  bisim1BlockNone bisim1BlockThrowNone
  bisim1Sync1 bisim1Sync2 bisim1Sync3 bisim1Sync4 bisim1Sync5 bisim1Sync6
  bisim1Sync7 bisim1Sync8 bisim1Sync9 bisim1Sync10 bisim1Sync11 bisim1Sync12
  bisim1Sync13 bisim1Sync14 bisim1Sync15 bisim1SyncThrow
  bisim1Seq1 bisim1SeqThrow1 bisim1Seq2
  bisim1Cond1 bisim1CondThen bisim1CondElse bisim1CondThrow
  bisim1While1 bisim1While3 bisim1While4
  bisim1While6 bisim1While7 bisim1WhileThrow1 bisim1WhileThrow2
  bisim1Throw1 bisim1Throw2 bisim1ThrowNull bisim1ThrowThrow
  bisim1Try bisim1TryCatch1 bisim1TryCatch2 bisim1TryFail bisim1TryCatchThrow
  bisims1Nil bisims1List1 bisims1List2]

lemmas bisim1_bisims1_inducts_split = bisim1_bisims1_inducts[split_format (complete)]

lemma bisim1_pc_length_compE2: "P,E,n,h \<turnstile> (e, xs) \<leftrightarrow> (stk, loc, pc, xcp) \<Longrightarrow> pc \<le> length (compE2 E)"
  and bisims1_pc_length_compEs2: "P,Es,n,h \<turnstile> (es, xs) [\<leftrightarrow>] (stk, loc, pc, xcp) \<Longrightarrow> pc \<le> length (compEs2 Es)"
apply(induct rule: bisim1_bisims1_inducts_split)
apply(auto)
done

lemma bisim1_pc_length_compE2D:
  "P,e,n,h \<turnstile> (e', xs) \<leftrightarrow> (stk,loc,length (compE2 e),xcp)
  \<Longrightarrow> xcp = None \<and> call e' = None \<and> (\<exists>v. stk = [v] \<and> (is_val e' \<longrightarrow> e' = Val v \<and> xs = loc))"

  and bisims1_pc_length_compEs2D:
  "P,es,n,h \<turnstile> (es', xs) [\<leftrightarrow>] (stk,loc,length (compEs2 es),xcp)
  \<Longrightarrow> xcp = None \<and> calls es' = None \<and> (\<exists>vs. stk = rev vs \<and> length vs = length es \<and> (is_vals es' \<longrightarrow> es' = map Val vs \<and> xs = loc))"
proof(induct e n e' xs stk loc pc\<equiv>"length (compE2 e)" xcp
         and es n es' xs stk loc pc\<equiv>"length (compEs2 es)" xcp
        rule: bisim1_bisims1_inducts_split)
  case (bisims1List2 es n es' xs stk loc pc xcp e v)
  then obtain vs where "xcp = None" "calls es' = None" 
    "stk = rev vs" "length vs = length es" "is_vals es' \<longrightarrow> es' = map Val vs \<and> xs = loc" by auto
  thus ?case 
    by(clarsimp)(rule_tac x="v#vs" in exI, auto)
qed(simp_all (no_asm_use), (fastsimp dest: bisim1_pc_length_compE2 bisims1_pc_length_compEs2 split: bop.split_asm split_if_asm)+)


corollary bisim1_call_pcD: "\<lbrakk> P,e,n,h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, xcp); call e' = \<lfloor>aMvs\<rfloor> \<rbrakk> \<Longrightarrow> pc < length (compE2 e)"
  and bisims1_calls_pcD: "\<lbrakk> P,es,n,h \<turnstile> (es', xs) [\<leftrightarrow>] (stk, loc, pc, xcp); calls es' = \<lfloor>aMvs\<rfloor> \<rbrakk> \<Longrightarrow> pc < length (compEs2 es)"
proof -
  assume bisim: "P,e,n,h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, xcp)"
    and call: "call e' = \<lfloor>aMvs\<rfloor>"

  { assume "pc = length (compE2 e)"
    with bisim call have False
      by(auto dest: bisim1_pc_length_compE2D) }
  moreover from bisim have "pc \<le> length (compE2 e)"
    by(rule bisim1_pc_length_compE2)
  ultimately show "pc < length (compE2 e)"
    by(cases "pc < length (compE2 e)")(auto)
next
  assume bisim: "P,es,n,h \<turnstile> (es', xs) [\<leftrightarrow>] (stk, loc, pc, xcp)"
    and call: "calls es' = \<lfloor>aMvs\<rfloor>"
  { assume "pc = length (compEs2 es)"
    with bisim call have False
      by(auto dest: bisims1_pc_length_compEs2D) }
  moreover from bisim have "pc \<le> length (compEs2 es)"
    by(rule bisims1_pc_length_compEs2)
  ultimately show "pc < length (compEs2 es)"
    by(cases "pc < length (compEs2 es)")(auto)
qed

lemma bisim1_length_xs: "P,e,n,h \<turnstile> (e',xs) \<leftrightarrow> (stk, loc, pc, xcp) \<Longrightarrow> length xs = length loc"
  and bisims1_length_xs: "P,es,n,h \<turnstile> (es',xs) [\<leftrightarrow>] (stk, loc, pc, xcp) \<Longrightarrow> length xs = length loc"
by(induct rule: bisim1_bisims1_inducts_split)(auto)

lemma bisim1_Val_length_compE2D:
  "P,e,n,h \<turnstile> (Val v,xs) \<leftrightarrow> (stk, loc, length (compE2 e), xcp) \<Longrightarrow> stk = [v] \<and> xs = loc \<and> xcp = None"

  and bisims1_Val_length_compEs2D:
  "P,es,n,h \<turnstile> (map Val vs,xs) [\<leftrightarrow>] (stk, loc, length (compEs2 es), xcp) \<Longrightarrow> stk = rev vs \<and> xs = loc \<and> xcp = None"
by(auto dest: bisim1_pc_length_compE2D bisims1_pc_length_compEs2D)

lemma bisim_Val_loc_eq_xcp_None: "P, e, n, h \<turnstile> (Val v,xs) \<leftrightarrow> (stk,loc,pc,xcp) \<Longrightarrow> xs = loc \<and> xcp = None"
  and bisims_Val_loc_eq_xcp_None: "P, es, n, h \<turnstile> (map Val vs,xs) [\<leftrightarrow>] (stk,loc,pc,xcp) \<Longrightarrow> xs = loc \<and> xcp = None"
apply(induct e n e'\<equiv>"Val v::expr1" xs stk loc pc xcp
         and es n es'\<equiv>"map Val vs::expr1 list" xs stk loc pc xcp
        arbitrary: v and vs rule: bisim1_bisims1_inducts_split)
apply(auto)
done

lemma bisim_Val_pc_not_Invoke: 
  "\<lbrakk> P,e,n,h \<turnstile> (Val v,xs) \<leftrightarrow> (stk,loc,pc,xcp); pc < length (compE2 e) \<rbrakk> \<Longrightarrow> compE2 e ! pc \<noteq> Invoke M n'"

  and bisims_Val_pc_not_Invoke: 
  "\<lbrakk> P,es,n,h \<turnstile> (map Val vs,xs) [\<leftrightarrow>] (stk,loc,pc,xcp); pc < length (compEs2 es) \<rbrakk> \<Longrightarrow> compEs2 es ! pc \<noteq> Invoke M n'"
apply(induct e n e'\<equiv>"Val v::expr1" xs stk loc pc xcp
         and es n es'\<equiv>"map Val vs::expr1 list" xs stk loc pc xcp
  arbitrary: v and vs rule: bisim1_bisims1_inducts_split)
apply(auto simp add: nth_append compEs2_map_Val nth_Cons_subtract dest: bisim1_pc_length_compE2)
done

lemma bisim1_VarD: "P, E, n, h \<turnstile> (Var V,xs) \<leftrightarrow> (stk,loc,pc,xcp) \<Longrightarrow> xs = loc"
  and "P, es, n, h \<turnstile> (es', xs) [\<leftrightarrow>] (stk, loc, pc, xcp) \<Longrightarrow> True"
by(induct E n e\<equiv>"(Var V :: expr1)" xs stk loc pc xcp and rule: bisim1_bisims1_inducts_split)(auto)


lemma bisim1_ThrowD:
  "P, e, n, h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, xcp)
  \<Longrightarrow> pc < length (compE2 e) \<and> (xcp = \<lfloor>a\<rfloor> \<or> xcp = None) \<and> xs = loc"

  and bisims1_ThrowD:
  "P, es, n, h \<turnstile> (map Val vs @ Throw a # es', xs) [\<leftrightarrow>] (stk, loc, pc, xcp)
  \<Longrightarrow> pc < length (compEs2 es) \<and> (xcp = \<lfloor>a\<rfloor> \<or> xcp = None) \<and> xs = loc"
apply(induct e n e'\<equiv>"Throw a::expr1" xs stk loc pc xcp
         and es n es''\<equiv>"map Val vs @ Throw a # es'::expr1 list" xs stk loc pc xcp
         arbitrary: and vs es' rule: bisim1_bisims1_inducts_split)
apply(fastsimp dest: bisim1_pc_length_compE2 bisim_Val_loc_eq_xcp_None simp add: Cons_eq_append_conv)+
done


lemma fixes P :: J1_prog
  shows bisim1_Invoke_stkD:
  "\<lbrakk> P,e,n,h \<turnstile> (e', xs) \<leftrightarrow> (stk,loc,pc,None); pc < length (compE2 e); compE2 e ! pc = Invoke M n' \<rbrakk> 
  \<Longrightarrow> \<exists>vs v stk'. stk = vs @ v # stk' \<and> length vs = n'"

  and bisims1_Invoke_stkD: 
  "\<lbrakk> P,es,n,h \<turnstile> (es', xs) [\<leftrightarrow>] (stk,loc,pc,None); pc < length (compEs2 es); compEs2 es ! pc = Invoke M n' \<rbrakk>
  \<Longrightarrow> \<exists>vs v stk'. stk = vs @ v # stk' \<and> length vs = n'"
proof(induct e n e' xs stk loc pc xcp\<equiv>"None::addr option"
         and es n es' xs stk loc pc xcp\<equiv>"None::addr option" rule: bisim1_bisims1_inducts_split)
  case bisim1Call1
  thus ?case
    apply(clarsimp simp add: nth_append append_eq_append_conv2 neq_Nil_conv split: split_if_asm)
    apply(drule bisim1_pc_length_compE2, clarsimp simp add: neq_Nil_conv nth_append)
    apply(frule bisim1_pc_length_compE2, clarsimp)
    apply(drule bisim1_pc_length_compE2D, fastsimp)
    done
next
  case bisim1CallParams thus ?case
    apply(clarsimp simp add: nth_append append_eq_Cons_conv split: split_if_asm)
    apply(fastsimp simp add: append_eq_append_conv2 Cons_eq_append_conv)
    apply(frule bisims1_pc_length_compEs2, clarsimp)
    apply(drule bisims1_pc_length_compEs2D, fastsimp simp add: append_eq_append_conv2)
    done
qed(fastsimp simp add: nth_append append_eq_append_conv2 neq_Nil_conv nth_Cons_subtract split: split_if_asm bop.split_asm dest: bisim1_pc_length_compE2 bisims1_pc_length_compEs2)+

lemma fixes P :: J1_prog
  shows bisim1_call_xcpNone: "P,e,n,h \<turnstile> (e',xs) \<leftrightarrow> (stk,loc,pc,\<lfloor>a\<rfloor>) \<Longrightarrow> call e' = None"
  and bisims1_calls_xcpNone: "P,es,n,h \<turnstile> (es',xs) [\<leftrightarrow>] (stk,loc,pc,\<lfloor>a\<rfloor>) \<Longrightarrow> calls es' = None"
apply(induct e n e' xs stk loc pc xcp\<equiv>"\<lfloor>a::addr\<rfloor>" and es n es' xs stk loc pc xcp\<equiv>"\<lfloor>a::addr\<rfloor>" rule: bisim1_bisims1_inducts_split)
apply(auto dest: bisim_Val_loc_eq_xcp_None bisims_Val_loc_eq_xcp_None simp add: is_vals_conv)
done


lemma bisims1_map_Val_append:
  assumes bisim: "P, es', n, h \<turnstile> (es'', xs) [\<leftrightarrow>] (stk, loc, pc, xcp)"
  and Bs: "bsoks es n"
  shows "length es = length vs
          \<Longrightarrow> P, es @ es', n, h \<turnstile> (map Val vs @ es'', xs) [\<leftrightarrow>] (stk @ rev vs, loc, length (compEs2 es) + pc, xcp)"
using Bs
proof(induct vs arbitrary: es)
  case Nil thus ?case using bisim by simp
next
  case (Cons v vs)
  note IH = `\<And>es. \<lbrakk> length es = length vs; bsoks es n \<rbrakk> \<Longrightarrow> P,es @ es',n,h \<turnstile> (map Val vs @ es'',xs) [\<leftrightarrow>] (stk @ rev vs,loc,length (compEs2 es) + pc,xcp)`
  from `length es = length (v # vs)` obtain e es''' where [simp]: "es = e # es'''" by(cases es, auto)
  with `length es = length (v # vs)` have len: "length es''' = length vs" by simp
  from `bsoks es n` have "bsok e n" "bsoks es''' n"
    by(auto simp add: nat_fun_sum_eq_conv)
  from IH[OF len `bsoks es''' n`] `bsok e n`
  show ?case by(simp add: add_assoc append_assoc[symmetric] del: append_assoc)(rule bisims1List2, auto)
qed

lemma bisim1_hext_mono: "\<lbrakk> P,e,n,h \<turnstile> exs \<leftrightarrow> s; hext h h' \<rbrakk> \<Longrightarrow> P,e,n,h' \<turnstile> exs \<leftrightarrow> s"
  and bisims1_hext_mono: "\<lbrakk> P,es,n,h \<turnstile> esxs [\<leftrightarrow>] s; hext h h' \<rbrakk> \<Longrightarrow> P,es,n,h' \<turnstile> esxs [\<leftrightarrow>] s"
proof -
  assume hext: "hext h h'"
  have "P,e,n,h \<turnstile> exs \<leftrightarrow> s \<Longrightarrow> P,e,n,h' \<turnstile> exs \<leftrightarrow> s"
    and "P,es,n,h \<turnstile> esxs [\<leftrightarrow>] s \<Longrightarrow> P,es,n,h' \<turnstile> esxs [\<leftrightarrow>] s"
    apply(induct rule: bisim1_bisims1.inducts)
    apply(insert hext)
    apply(auto intro: bisim1_bisims1.intros dest: hext_objD)
    done
  thus "\<lbrakk> P,e,n,h \<turnstile> exs \<leftrightarrow> s; hext h h' \<rbrakk> \<Longrightarrow> P,e,n,h' \<turnstile> exs \<leftrightarrow> s"
    and "\<lbrakk> P,es,n,h \<turnstile> esxs [\<leftrightarrow>] s; hext h h' \<rbrakk> \<Longrightarrow> P,es,n,h' \<turnstile> esxs [\<leftrightarrow>] s" by auto
qed

declare match_ex_table_append_not_pcs [simp]
       match_ex_table_eq_NoneI[simp]
       outside_pcs_compxE2_not_matches_entry[simp]
       outside_pcs_compxEs2_not_matches_entry[simp]

lemma bisim1_xcp_Some_not_caught:
  "P, e, n, h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)
  \<Longrightarrow> match_ex_table (compP f P) (cname_of h a) (pc' + pc) (compxE2 e pc' d) = None"

  and bisims1_xcp_Some_not_caught:
  "P, es, n, h \<turnstile> (map Val vs @ Throw a # es', xs) [\<leftrightarrow>] (stk, loc, pc, \<lfloor>a\<rfloor>)
  \<Longrightarrow> match_ex_table (compP f P) (cname_of h a) (pc' + pc) (compxEs2 es pc' d) = None"
proof(induct e n e'\<equiv>"Throw a::expr1" xs stk loc pc xcp\<equiv>"\<lfloor>a\<rfloor>::addr option"
         and es n es''\<equiv>"map Val vs @ Throw a # es'::expr1 list" xs stk loc pc xcp\<equiv>"\<lfloor>a\<rfloor>::addr option"
      arbitrary: pc' d and vs es' pc' d rule: bisim1_bisims1_inducts_split)
  case bisim1Sync10
  thus ?case by(simp add: matches_ex_entry_def)
next
  case bisim1Sync11
  thus ?case by(simp add: matches_ex_entry_def)
next
  case (bisim1SyncThrow e1 V a' xs stk loc pc e2)
  hence IH: "\<And>pc' d. match_ex_table (compP f P) (cname_of h a) (pc' + pc) (compxE2 e1 pc' d) = None"
    and [simp]: "a' = a" by auto
  from `P,e1,V,h \<turnstile> (Throw a',xs) \<leftrightarrow> (stk,loc,pc,\<lfloor>a'\<rfloor>)` have "pc < length (compE2 e1)" by(auto dest: bisim1_ThrowD)
  with IH[of pc' d] show ?case
    by(auto simp add: match_ex_table_append matches_ex_entry_def dest: match_ex_table_pc_length_compE2)
next
  case bisims1List1 thus ?case
    by(auto simp add: Cons_eq_append_conv dest: bisim1_ThrowD bisim_Val_loc_eq_xcp_None)
next
  case (bisims1List2 es n es'' xs stk loc pc xcp e v)
  hence "\<And>pc' d. match_ex_table (compP f P) (cname_of h a) (pc' + pc) (compxEs2 es pc' d) = None"
    by(auto simp add: Cons_eq_append_conv)
  from this[of "pc' + length (compE2 e)" "Suc d"] show ?case by(auto simp add: add_assoc)
next
  case (bisim1BlockThrowSome e V a' xs stk loc pc T v)
  hence "\<And>pc'. match_ex_table (compP f P) (cname_of h a) (pc' + pc) (compxE2 e pc' d) = None" by auto
  from this[of "2+pc'"] show ?case by(auto)
next
  case (bisim1Seq2 e2 n e' xs stk loc pc xcp e1)
  hence "\<And>pc'. match_ex_table (compP f P) (cname_of h a) (pc' + pc) (compxE2 e2 pc' d) = None" by auto
  from this[of "Suc (pc' + length (compE2 e1))"] show ?case by(simp add: add_assoc)
next
  case (bisim1CondThen e1 n e' xs stk loc pc xcp e e2)
  hence "\<And>pc'. match_ex_table (compP f P) (cname_of h a) (pc' + pc) (compxE2 e1 pc' d) = None" by auto
  note this[of "Suc (pc' + length (compE2 e))"]
  moreover from `P,e1,n,h \<turnstile> (e',xs) \<leftrightarrow> (stk,loc,pc,xcp)` `e' = Throw a`
  have "pc < length (compE2 e1)" by(auto dest: bisim1_ThrowD)
  ultimately show ?case by(simp add: add_assoc match_ex_table_eq_NoneI outside_pcs_compxE2_not_matches_entry)
next
  case (bisim1CondElse e2 n e' xs stk loc pc xcp e e1)
  hence "\<And>pc'. match_ex_table (compP f P) (cname_of h a) (pc' + pc) (compxE2 e2 pc' d) = None" by auto
  note this[of "Suc (Suc (pc' + (length (compE2 e) + length (compE2 e1))))"]
  thus ?case by(simp add: add_assoc)
next
  case (bisim1WhileThrow2 e n a' xs stk loc pc c)
  hence "\<And>pc'. match_ex_table (compP f P) (cname_of h a) (pc' + pc) (compxE2 e pc' d) = None" by auto
  from this[of "Suc (pc' + (length (compE2 c)))"]
  show ?case by(simp add: add_assoc)
next
  case (bisim1Throw1 e n e' xs stk loc pc xcp)
  from `throw e' = Throw a` have "e' = addr a" by simp
  with `P,e,n,h \<turnstile> (e',xs) \<leftrightarrow> (stk,loc,pc,xcp)` have "P,e,n,h \<turnstile> (addr a,xs) \<leftrightarrow> (stk,loc,pc,xcp)" by simp
  hence "xcp = None" by(auto dest: bisim_Val_loc_eq_xcp_None)
  with `xcp = \<lfloor>a\<rfloor>` show ?case by(simp)
next
  case (bisim1TryFail e V a' xs stk loc pc C' fs C e2)
  hence "match_ex_table (compP f P) (cname_of h a) (pc' + pc) (compxE2 e pc' d) = None" by auto
  moreover from `P,e,V,h \<turnstile> (Throw a',xs) \<leftrightarrow> (stk,loc,pc,\<lfloor>a'\<rfloor>)` have "pc < length (compE2 e)"
    by(auto dest: bisim1_ThrowD)
  ultimately show ?case using `h a' = \<lfloor>Obj C' fs\<rfloor>` `\<not> P \<turnstile> C' \<preceq>\<^sup>* C` `\<lfloor>a'\<rfloor> = \<lfloor>a\<rfloor>`
    by(simp add: matches_ex_entry_def)
next
  case (bisim1TryCatchThrow e2 V a' xs stk loc pc e C)
  hence "\<And>pc'. match_ex_table (compP f P) (cname_of h a) (pc' + pc) (compxE2 e2 pc' d) = None" by auto
  from this[of "Suc (Suc (pc' + (length (compE2 e))))"]
  show ?case by(simp add: add_assoc matches_ex_entry_def)
next
  case bisim1Sync12 thus ?case
    by(auto dest: bisim1_ThrowD simp add: match_ex_table_append nat_number, simp add: matches_ex_entry_def)
next
  case bisim1Sync13 thus ?case
    by(auto dest: bisim1_ThrowD simp add: match_ex_table_append nat_number, simp add: matches_ex_entry_def)
next
  case bisim1Sync14 thus ?case
    by(auto dest: bisim1_ThrowD simp add: match_ex_table_append nat_number, simp add: matches_ex_entry_def)
next
  case bisim1Sync15 thus ?case
    by(auto dest: bisim1_ThrowD simp add: match_ex_table_append nat_number, simp add: matches_ex_entry_def)
qed(fastsimp dest: bisim1_ThrowD simp add: add_assoc[symmetric])+

declare match_ex_table_append_not_pcs [simp del]
       match_ex_table_eq_NoneI[simp del]
       outside_pcs_compxE2_not_matches_entry[simp del]
       outside_pcs_compxEs2_not_matches_entry[simp del]

lemma bisim1_xcp_pcD: "P,e,n,h \<turnstile> (e', xs ) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>) \<Longrightarrow> pc < length (compE2 e)"
  and bisims1_xcp_pcD: "P,es,n,h \<turnstile> (es', xs ) [\<leftrightarrow>] (stk, loc, pc, \<lfloor>a\<rfloor>) \<Longrightarrow> pc < length (compEs2 es)"
by(induct e n e' xs stk loc pc xcp\<equiv>"\<lfloor>a::addr\<rfloor>" and es n es' xs stk loc pc xcp\<equiv>"\<lfloor>a::addr\<rfloor>"
    rule: bisim1_bisims1_inducts_split) auto


declare nth_Cons_subtract[simp]
declare nth_append [simp]

lemma bisim1_Val_\<tau>Exec_move:
  "\<lbrakk> P, E, n, h \<turnstile> (Val v, xs) \<leftrightarrow> (stk, loc, pc, xcp); pc < length (compE2 E); P,Env \<turnstile>1 E :: Typ \<rbrakk> 
  \<Longrightarrow> xs = loc \<and> xcp = None \<and>
     \<tau>Exec_move P E h (stk, xs, pc, None) ([v], xs, length (compE2 E), None)"

 and bisims1_Val_\<tau>Exec_moves:
  "\<lbrakk> P, Es, n, h \<turnstile> (map Val vs, xs) [\<leftrightarrow>] (stk, loc, pc, xcp); pc < length (compEs2 Es); P,Env \<turnstile>1 Es [::] Typs \<rbrakk> 
  \<Longrightarrow> xs = loc \<and> xcp = None \<and>
    \<tau>Exec_moves P Es h (stk, xs, pc, None) (rev vs, xs, length (compEs2 Es), None)"
proof(induct E n e\<equiv>"(Val v::expr1)" xs stk loc pc xcp
         and Es n es\<equiv>"map Val vs::expr1 list" xs stk loc pc xcp 
  arbitrary: v Env Typ and vs Env Typs rule: bisim1_bisims1_inducts_split)
  case bisim1Val thus ?case by(auto intro!: \<tau>Exec1step exec_instr \<tau>move2Val simp add: exec_move_def)
next
  case (bisim1LAss2 e n V xs)
  have "\<tau>Exec_move P (V:=e) h ([], xs, Suc (length (compE2 e)), None) ([Unit], xs, Suc (Suc (length (compE2 e))), None)"
    by(auto intro!: \<tau>Exec1step exec_instr \<tau>move2LAssRed simp add: nth_append exec_move_def)
  with bisim1LAss2 show ?case by simp
next
  case (bisim1AAss4 a n i e xs)
  have "\<tau>Exec_move P (a\<lfloor>i\<rceil> := e) h ([], xs, Suc (length (compE2 a) + length (compE2 i) + length (compE2 e)), None) ([Unit], xs, Suc (Suc (length (compE2 a) + length (compE2 i) + length (compE2 e))), None)"
    by(auto intro!: \<tau>Exec1step exec_instr \<tau>move2AAssRed simp add: nth_append exec_move_def)
  with bisim1AAss4 show ?case by(simp add: add_ac)
next
  case (bisim1FAss3 e n e2 F D xs)
  have "\<tau>Exec_move P (e\<bullet>F{D} := e2) h ([], xs, Suc (length (compE2 e) + length (compE2 e2)), None) ([Unit], xs, Suc (Suc (length (compE2 e) + length (compE2 e2))), None)"
    by(auto intro!: \<tau>Exec1step exec_instr \<tau>move2FAssRed simp add: nth_append exec_move_def)
  with bisim1FAss3 show ?case by simp
next
  case (bisim1Sync6 e1 V e2 v' xs)
  have "\<tau>Exec_move P (sync\<^bsub>V\<^esub> (e1) e2) h ([v], xs, 5 + length (compE2 e1) + length (compE2 e2), None)
                                        ([v], xs, 9 + length (compE2 e1) + length (compE2 e2), None)"
    by(rule \<tau>Exec1step)(auto intro: exec_instr \<tau>move2Sync6 simp add: exec_move_def)
  with bisim1Sync6 show ?case by(auto simp add: nat_number)
next
  case (bisim1Seq2 e2 n e' xs stk loc pc xcp e1)
  from `Suc (length (compE2 e1) + pc) < length (compE2 (e1;; e2))` have pc: "pc < length (compE2 e2)" by simp
  from `P,Env \<turnstile>1 e1;; e2 :: Typ` obtain T where "P,Env \<turnstile>1 e2 :: T" by auto
  with pc `e' = Val v` `\<lbrakk>pc < length (compE2 e2); P,Env \<turnstile>1 e2 :: T; e' = Val v\<rbrakk> \<Longrightarrow> xs = loc \<and> xcp = None \<and> \<tau>Exec_move P e2 h (stk, xs, pc, None) ([v], xs, length (compE2 e2), None)`
  have "xs = loc" "xcp = None"
    "\<tau>Exec_move P e2 h (stk, xs, pc, None) ([v], xs, length (compE2 e2), None)" by auto
  moreover 
  hence "\<tau>Exec_move P (e1;;e2) h (stk, xs, Suc (length (compE2 e1) + pc), None) ([v], xs, Suc (length (compE2 e1) + length (compE2 e2)), None)"
    by -(rule Seq_\<tau>Exec_meth_xt2)
  ultimately show ?case by(simp)
next
  case (bisim1CondThen e1 n e' xs stk loc pc xcp e e2)
  from `P, e1, n, h \<turnstile> (e',xs) \<leftrightarrow> (stk,loc,pc,xcp)`
  have "pc \<le> length (compE2 e1)" by(rule bisim1_pc_length_compE2)

  have e: "\<tau>Exec_move P (if (e) e1 else e2) h
                     ([v], xs, Suc (length (compE2 e) + (length (compE2 e1))), None)
                     ([v], xs, length (compE2 (if (e) e1 else e2)), None)" 
    by(rule \<tau>Exec1step)(auto simp add: nth_append exec_move_def intro!: exec_instr \<tau>move2CondThenExit)
  from `P,Env \<turnstile>1 if (e) e1 else e2 :: Typ` obtain T1 T2
    where wte: "P,Env \<turnstile>1 e :: Boolean" and wt1: "P,Env \<turnstile>1 e1 :: T1" and wt2: "P,Env \<turnstile>1 e2 :: T2" by auto

  show ?case
  proof(cases "pc < length (compE2 e1)")
    case True
    with `e' = Val v` wt1 `\<lbrakk>pc < length (compE2 e1); P,Env \<turnstile>1 e1 :: T1; e' = Val v\<rbrakk>
         \<Longrightarrow> xs = loc \<and> xcp = None \<and> \<tau>Exec_move P e1 h (stk, xs, pc, None) ([v], xs, length (compE2 e1), None)`
    have s: "xs = loc" "xcp = None"
      and "\<tau>Exec_move P e1 h (stk, xs, pc, None) ([v], xs, length (compE2 e1), None)" by auto
    hence "\<tau>Exec_move P (if (e) e1 else e2) h
                     (stk, xs, Suc (length (compE2 e) + pc), None)
                     ([v], xs, Suc (length (compE2 e) + length (compE2 e1)), None)"
      by -(rule Cond_\<tau>Exec_meth_xt_then)
    with e True s show ?thesis by(simp)(rule \<tau>Exec_move_trans)
  next
    case False
    with `pc \<le> length (compE2 e1)` have pc: "pc = length (compE2 e1)" by auto
    with `P, e1, n, h \<turnstile> (e',xs) \<leftrightarrow> (stk,loc,pc,xcp)` `e' = Val v`
    have "stk = [v]" "xs = loc" "xcp = None" by(auto dest: bisim1_Val_length_compE2D)
    with pc e show ?thesis by(simp)
  qed
next
  case (bisim1CondElse e2 n e' xs stk loc pc xcp e e1)
  from `P, e2, n, h \<turnstile> (e',xs) \<leftrightarrow> (stk,loc,pc,xcp)`
  have "pc \<le> length (compE2 e2)" by(rule bisim1_pc_length_compE2)
  from `P,Env \<turnstile>1 if (e) e1 else e2 :: Typ` obtain T1 T2
    where wte: "P,Env \<turnstile>1 e :: Boolean" and wt1: "P,Env \<turnstile>1 e1 :: T1" and wt2: "P,Env \<turnstile>1 e2 :: T2" by auto

  show ?case
  proof(cases "pc < length (compE2 e2)")
    case True
    with `e' = Val v` wt2 `\<lbrakk>pc < length (compE2 e2); P,Env \<turnstile>1 e2 :: T2; e' = Val v\<rbrakk>
         \<Longrightarrow> xs = loc \<and> xcp = None \<and> \<tau>Exec_move P e2 h (stk, xs, pc, None) ([v], xs, length (compE2 e2), None)`
    have s: "xs = loc" "xcp = None"
      and e: "\<tau>Exec_move P e2 h (stk, xs, pc, None) ([v], xs, length (compE2 e2), None)" by auto
    from e have "\<tau>Exec_move P (if (e) e1 else e2) h (stk, xs, Suc (Suc (length (compE2 e) + length (compE2 e1) + pc)), None) ([v], xs, Suc (Suc (length (compE2 e) + length (compE2 e1) + length (compE2 e2))), None)"
      by(rule Cond_\<tau>Exec_meth_xt_else)
    with True s show ?thesis by(simp add: add_assoc)
  next
    case False
    with `pc \<le> length (compE2 e2)` have pc: "pc = length (compE2 e2)" by auto
    with `P, e2, n, h \<turnstile> (e',xs) \<leftrightarrow> (stk,loc,pc,xcp)` `e' = Val v`
    have "stk = [v]" "xs = loc" "xcp = None" by(auto dest: bisim1_Val_length_compE2D)
    with pc show ?thesis by(simp add: add_assoc)(rule \<tau>Exec_refl)
  qed
next
  case (bisim1While7 c n e xs)
  have "\<tau>Exec_move P (while (c) e) h
                   ([], xs, Suc (Suc (Suc (length (compE2 c) + length (compE2 e)))), None)
                   ([Unit], xs, length (compE2 (while (c) e)), None)"
    by(auto intro!: \<tau>Exec1step exec_instr \<tau>move2While4 simp add: nth_append exec_move_def)
  with `unit = Val v` show ?case by(simp)
next
  case (bisims1List1 e n e' xs stk loc pc xcp es)
  from `e' # es = map Val vs` obtain v vs' where [simp]: "vs = v # vs'" "e' = Val v" "es = map Val vs'" by auto
  from `P,Env \<turnstile>1 e # es [::] Typs` obtain T Ts where wte: "P,Env \<turnstile>1 e :: T" and wtes: "P,Env \<turnstile>1 map Val vs' [::] Ts" by auto
  from `P,e,n,h \<turnstile> (e',xs) \<leftrightarrow> (stk,loc,pc,xcp)`
  have length: "pc \<le> length (compE2 e)" by(auto dest: bisim1_pc_length_compE2)
  hence "xs = loc \<and> xcp = None \<and> \<tau>Exec_move P e h (stk, xs, pc, None) ([v], xs, length (compE2 e), None)"
  proof(cases "pc < length (compE2 e)")
    case True
    with `\<lbrakk>pc < length (compE2 e); P,Env \<turnstile>1 e :: T; e' = Val v\<rbrakk> \<Longrightarrow> xs = loc \<and> xcp = None \<and> \<tau>Exec_move P e h (stk, xs, pc, None) ([v], xs, length (compE2 e), None)` wte
    have "xs = loc" "xcp = None"
      "\<tau>Exec_move P e h (stk, xs, pc, None) ([v], xs, length (compE2 e), None)" by auto
    thus ?thesis by auto
  next
    case False
    with length have pc: "pc = length (compE2 e)" by auto
    with `P,e,n,h \<turnstile> (e',xs) \<leftrightarrow> (stk,loc,pc,xcp)` have "stk = [v]" "xs = loc" "xcp = None"
      by(auto dest: bisim1_Val_length_compE2D)
    with pc show ?thesis by(auto intro: \<tau>Exec_refl)
  qed
  hence s: "xs = loc" "xcp = None"
    and exec1: "\<tau>Exec_move P e h (stk, xs, pc, None) ([v], xs, length (compE2 e), None)" by auto
  from exec1 wtes have "\<tau>Exec_moves P (e # es) h (stk, xs, pc, None) ([v], xs, length (compE2 e), None)"
    by(auto intro: \<tau>Exec_move_\<tau>Exec_moves)
  moreover from wtes have "\<tau>Exec_moves P (map Val vs') h ([], xs, 0, None) (rev vs', xs, length (compEs2 (map Val vs')), None)"
    by(rule \<tau>Exec_moves_map_Val)
  hence "\<tau>Exec_moves P ([e] @ map Val vs') h ([] @ [v], xs, length (compEs2 [e]) + 0, None) (rev vs' @ [v], xs, length (compEs2 [e]) + length (compEs2 (map Val vs')), None)"
    by -(rule append_\<tau>Exec_moves, auto)
  ultimately show ?case using s by(auto intro: \<tau>Exec_moves_trans)
next
  case (bisims1List2 es n es' xs stk loc pc xcp e v)
  from `Val v # es' = map Val vs` obtain vs' where [simp]: "vs = v # vs'" "es' = map Val vs'" by auto
  from `P,Env \<turnstile>1 e # es [::] Typs` obtain T Ts where wte: "P,Env \<turnstile>1 e :: T" and wtes: "P,Env \<turnstile>1 es [::] Ts" by auto
  from `P,es,n,h \<turnstile> (es',xs) [\<leftrightarrow>] (stk,loc,pc,xcp)`
  have length: "pc \<le> length (compEs2 es)" by(auto dest: bisims1_pc_length_compEs2)
  hence "xs = loc \<and> xcp = None \<and> \<tau>Exec_moves P es h (stk, xs, pc, None) (rev vs', xs, length (compEs2 es), None)"
  proof(cases "pc < length (compEs2 es)")
    case True
    with `\<lbrakk>pc < length (compEs2 es); P,Env \<turnstile>1 es [::] Ts; es' = map Val vs'\<rbrakk> \<Longrightarrow> xs = loc \<and> xcp = None \<and> \<tau>Exec_moves P es h (stk, xs, pc, None)
      (rev vs', xs, length (compEs2 es), None)` wtes
    show ?thesis by auto
  next
    case False
    with length have pc: "pc = length (compEs2 es)" by auto
    with `P,es,n,h \<turnstile> (es',xs) [\<leftrightarrow>] (stk,loc,pc,xcp)` have "stk = rev vs'" "xs = loc" "xcp = None"
      by(auto dest: bisims1_Val_length_compEs2D)
    with pc show ?thesis by(auto intro: \<tau>Execs_refl)
  qed
  hence s: "xs = loc" "xcp = None"
    and exec1: "\<tau>Exec_moves P es h (stk, xs, pc, None) (rev vs', xs, length (compEs2 es), None)" by auto
  from exec1 have "\<tau>Exec_moves P ([e] @ es) h (stk @ [v], xs, length (compEs2 [e]) + pc, None) (rev vs' @ [v], xs, length (compEs2 [e]) + length (compEs2 es), None)"
    by -(rule append_\<tau>Exec_moves, auto)
  thus ?case using s by(auto)
qed(auto)

lemma bisim1Val2D1:
  assumes bisim: "P, e, n, h \<turnstile> (Val v,xs) \<leftrightarrow> (stk,loc,pc,xcp)"
  and wt: "P,Env \<turnstile>1 e :: T"
  shows "xcp = None \<and> xs = loc \<and> \<tau>Exec_move P e h (stk, loc, pc, xcp) ([v], loc, length (compE2 e), None)"
proof -
  from bisim have "xcp = None" "xs = loc" by(auto dest: bisim_Val_loc_eq_xcp_None)
  moreover 
  have "\<tau>Exec_move P e h (stk, loc, pc, xcp) ([v], loc, length (compE2 e), None)"
  proof(cases "pc < length (compE2 e)")
    case True
    from bisim1_Val_\<tau>Exec_move[OF bisim True wt] show ?thesis by auto
  next
    case False
    from bisim have "pc \<le> length (compE2 e)" by(auto dest: bisim1_pc_length_compE2)
    with False have "pc = length (compE2 e)" by auto
    with bisim have "stk = [v]" "loc = xs" "xcp=None" by(auto dest: bisim1_Val_length_compE2D)
    with `pc = length (compE2 e)` show ?thesis by(auto intro: \<tau>Exec_refl)
  qed
  ultimately show ?thesis by simp
qed

lemma bisim1_Throw_\<tau>Exec_move:
  "\<lbrakk> P, e, n, h \<turnstile> (Throw a,xs) \<leftrightarrow> (stk,loc,pc,None); P, Env \<turnstile>1 e :: T \<rbrakk>
  \<Longrightarrow> \<exists>pc'. \<tau>Exec_move P e h (stk, loc, pc, None) ([Addr a], loc, pc', \<lfloor>a\<rfloor>) \<and>
      P, e, n, h \<turnstile> (Throw a,xs) \<leftrightarrow> ([Addr a], loc, pc', \<lfloor>a\<rfloor>) \<and> xs = loc"

  and bisims1_Throw_\<tau>Exec_moves:
  "\<lbrakk> P, es, n, h \<turnstile>  (map Val vs @ Throw a # es',xs) [\<leftrightarrow>] (stk,loc,pc,None); P,Env \<turnstile>1 es [::] Ts \<rbrakk>
  \<Longrightarrow> \<exists>pc'. \<tau>Exec_moves P es h (stk, loc, pc, None) (Addr a # rev vs, loc, pc', \<lfloor>a\<rfloor>) \<and>
      P, es, n, h \<turnstile> (map Val vs @ Throw a # es',xs) [\<leftrightarrow>] (Addr a # rev vs, loc, pc', \<lfloor>a\<rfloor>) \<and> xs = loc"
proof(induct e n e'\<equiv>"Throw a::expr1" xs stk loc pc xcp\<equiv>"None::addr option"
         and es n es''\<equiv>"map Val vs @ Throw a # es'::expr1 list" xs stk loc pc xcp\<equiv>"None::addr option"
         arbitrary: Env T and vs Env Ts rule: bisim1_bisims1_inducts_split)
  case (bisim1Sync9 e1 V e2 A xs)
  hence [simp]: "A = a" by simp
  let ?pc = "8 + length (compE2 e1) + length (compE2 e2)"
  have "\<tau>Exec_move P (sync\<^bsub>V\<^esub> (e1) e2) h ([Addr a], xs, ?pc, None) ([Addr a], xs, ?pc, \<lfloor>a\<rfloor>)"
    by(rule \<tau>Exec1step)(auto intro: exec_instr \<tau>move2_\<tau>moves2.intros simp add: is_Ref_def exec_move_def)
  moreover from `bsok e1 V` `bsok e2 (Suc V)`
  have "P,sync\<^bsub>V\<^esub> (e1) e2,V,h \<turnstile> (Throw a,xs) \<leftrightarrow> ([Addr a],xs,?pc,\<lfloor>a\<rfloor>)" by(rule bisim1Sync10)
  ultimately show ?case by auto
next
  case (bisim1Seq2 e2 n e' xs stk loc pc xcp e1)
  then obtain pc' where "\<tau>Exec_move P e2 h (stk, loc, pc, None) ([Addr a], loc, pc', \<lfloor>a\<rfloor>)"
    "P, e2, n, h \<turnstile> (Throw a,xs) \<leftrightarrow> ([Addr a],loc,pc',\<lfloor>a\<rfloor>)" "xs = loc" by auto
  with `bsok e1 n` show ?case by(auto intro: Seq_\<tau>Exec_meth_xt2 bisim1_bisims1.bisim1Seq2)
next
  case (bisim1CondThen e1 n e' xs stk loc pc xcp e e2)
  then obtain pc' where exec: "\<tau>Exec_move P e1 h (stk, loc, pc, None) ([Addr a], loc, pc', \<lfloor>a\<rfloor>)"
    and bisim: "P, e1, n, h \<turnstile> (Throw a,xs) \<leftrightarrow> ([Addr a],loc,pc',\<lfloor>a\<rfloor>)" and s: "xs = loc" by auto
  from exec have "\<tau>Exec_move P (if (e) e1 else e2) h (stk, loc, Suc (length (compE2 e) + pc), None) ([Addr a], loc, Suc (length (compE2 e) + pc'), \<lfloor>a\<rfloor>)"
    by(rule Cond_\<tau>Exec_meth_xt_then)
  moreover from bisim `bsok e n` `bsok e2 n`
  have "P, if (e) e1 else e2, n, h \<turnstile> (Throw a, xs) \<leftrightarrow> ([Addr a], loc, Suc (length (compE2 e) + pc'), \<lfloor>a\<rfloor>)"
    by(rule bisim1_bisims1.bisim1CondThen)
  ultimately show ?case using s by(auto)
next
  case (bisim1CondElse e2 n e' xs stk loc pc xcp e e1)
  then obtain pc' where exec: "\<tau>Exec_move P e2 h (stk, loc, pc, None) ([Addr a], loc, pc', \<lfloor>a\<rfloor>)"
    and bisim: "P, e2, n, h \<turnstile> (Throw a, xs ) \<leftrightarrow> ([Addr a], loc, pc', \<lfloor>a\<rfloor>)" and s: "xs = loc" by auto
  let "?pc pc" = "Suc (Suc (length (compE2 e) + length (compE2 e1) + pc))"
  from exec have "\<tau>Exec_move P (if (e) e1 else e2) h (stk, loc, (?pc pc), None) ([Addr a], loc, ?pc pc', \<lfloor>a\<rfloor>)"
    by(rule Cond_\<tau>Exec_meth_xt_else)
  moreover from bisim `bsok e n` `bsok e1 n`
  have "P, if (e) e1 else e2, n, h \<turnstile> (Throw a, xs ) \<leftrightarrow> ([Addr a], loc, ?pc pc', \<lfloor>a\<rfloor>)"
    by(rule bisim1_bisims1.bisim1CondElse)
  ultimately show ?case using s by auto
next
  case (bisim1Throw1 e n e' xs stk loc pc xcp)
  note bisim = `P, e, n, h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, xcp)`
  from `throw e' = Throw a` have e': "e' = addr a" by simp
  with bisim `P,Env \<turnstile>1 throw e :: T` have s: "xs = loc" 
    and exec: "\<tau>Exec_move P e h (stk, loc, pc, None) ([Addr a], loc, length (compE2 e), None)"
    by(auto dest: bisim1Val2D1)
  from exec have "\<tau>Exec_move P (throw e) h (stk, loc, pc, None) ([Addr a], loc, length (compE2 e), None)"
    by(rule Throw_\<tau>Exec_meth_xt)
  also have "\<tau>Exec_move P (throw e) h ([Addr a], loc, length (compE2 e), None) ([Addr a], loc, length (compE2 e), \<lfloor>a\<rfloor>)"
    by(rule \<tau>Exec1step, auto intro: exec_instr \<tau>move2Throw2 simp add: is_Ref_def exec_move_def)
  also from bisim have bs: "bsok e n" by(auto dest: bisim1_bsok)
  hence "P, throw e, n, h \<turnstile> (Throw a, loc ) \<leftrightarrow> ([Addr a], loc, length (compE2 e), \<lfloor>a\<rfloor>)"
    by(rule bisim1Throw2)
  ultimately show ?case using s by auto
next
  case (bisims1List1 e n e' xs stk loc pc xcp es)
  note bisim = `P,e,n,h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, xcp)`
  note B = `bsok e n`
  from `P,Env \<turnstile>1 e # es [::] Ts` `e' # es = map Val vs @ Throw a # es'`
  obtain T Ts' where wte: "P,Env \<turnstile>1 e :: T" and wtes: "P,Env \<turnstile>1 map Val vs [::] Ts'"
    by(fastsimp simp add: Cons_eq_append_conv elim: WTs1_append)
  show ?case
  proof(cases "is_val e'")
    case True
    with `e' # es = map Val vs @ Throw a # es'` `P,Env \<turnstile>1 e # es [::] Ts`
    have False by(auto simp add: Cons_eq_append_conv elim: WTs1_append)
    thus ?thesis ..
  next
    case False
    with `e' # es = map Val vs @ Throw a # es'` have [simp]: "e' = Throw a" "es = es'" "vs = []"
      by(auto simp add: Cons_eq_append_conv)
    from `\<lbrakk>P,Env \<turnstile>1 e :: T; e' = Throw a; xcp = None\<rbrakk> \<Longrightarrow> \<exists>pc'. \<tau>Exec_move P e h (stk, loc, pc, None) ([Addr a], loc, pc', \<lfloor>a\<rfloor>) \<and> P,e,n,h \<turnstile> (Throw a, xs ) \<leftrightarrow> ([Addr a], loc, pc', \<lfloor>a\<rfloor>) \<and> xs = loc` `xcp = None` wte
    obtain pc' where "\<tau>Exec_move P e h (stk, loc, pc, None) ([Addr a], loc, pc', \<lfloor>a\<rfloor>)"
      and bisim: "P,e,n,h \<turnstile> (Throw a, xs ) \<leftrightarrow> ([Addr a], loc, pc', \<lfloor>a\<rfloor>)" and s: "xs = loc" by auto
    hence "\<tau>Exec_moves P (e # es) h (stk, loc, pc, None) ([Addr a], loc, pc', \<lfloor>a\<rfloor>)"
      by-(rule \<tau>Exec_move_\<tau>Exec_moves)
    moreover from bisim `bsoks es n`
    have "P,e#es,n,h \<turnstile> (Throw a#es,xs) [\<leftrightarrow>] ([Addr a],loc,pc',\<lfloor>a\<rfloor>)" by(rule bisim1_bisims1.bisims1List1)
    ultimately show ?thesis using s by auto
  qed
next
  case (bisims1List2 es n es'' xs stk loc pc xcp e v)
  from `P,Env \<turnstile>1 e # es [::] Ts` obtain Ts' where wtes: "P,Env \<turnstile>1 es [::] Ts'" by auto
  note IH = `\<And>vs. \<lbrakk>P,Env \<turnstile>1 es [::] Ts'; es'' = map Val vs @ Throw a # es'; xcp = None\<rbrakk>
    \<Longrightarrow> \<exists>pc'. \<tau>Exec_moves P es h (stk, loc, pc, None) (Addr a # rev vs, loc, pc', \<lfloor>a\<rfloor>) \<and>
           P,es,n,h \<turnstile> (map Val vs @ Throw a # es',xs) [\<leftrightarrow>] (Addr a # rev vs,loc,pc',\<lfloor>a\<rfloor>) \<and> xs = loc`
  from `Val v # es'' = map Val vs @ Throw a # es'`
  obtain vs' where [simp]: "vs = v # vs'" "es'' = map Val vs' @ Throw a # es'" by(auto simp add: Cons_eq_append_conv)
  from IH[OF wtes `es'' = map Val vs' @ Throw a # es'` `xcp = None`]
  obtain pc' where exec: "\<tau>Exec_moves P es h (stk, loc, pc, None) (Addr a # rev vs', loc, pc', \<lfloor>a\<rfloor>)"
    and bisim: "P,es,n,h \<turnstile> (map Val vs' @ Throw a # es',xs) [\<leftrightarrow>] (Addr a # rev vs',loc,pc',\<lfloor>a\<rfloor>)"
    and [simp]: "xs = loc" by auto
  from append_\<tau>Exec_moves[OF _ exec, of "[v]" "[e]"]
  have "\<tau>Exec_moves P (e # es) h (stk @ [v], loc, length (compE2 e) + pc, None) (Addr a # rev vs, loc, length (compE2 e) + pc', \<lfloor>a\<rfloor>)" by simp
  moreover from bisim `bsok e n`
  have "P,e#es,n,h \<turnstile> (Val v # map Val vs' @ Throw a # es',xs) [\<leftrightarrow>] ((Addr a # rev vs')@[v],loc,length (compE2 e) + pc',\<lfloor>a\<rfloor>)"
    by(rule bisim1_bisims1.bisims1List2)
  ultimately show ?case by(auto)
qed(auto)

declare split_beta [simp]

lemma bisim1_inline_call_Throw:
  "\<lbrakk> P,e,n,h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, None); call e' = \<lfloor>(a, M, vs)\<rfloor>;
     compE2 e ! pc = Invoke M (length vs); pc < length (compE2 e) \<rbrakk>
  \<Longrightarrow> P,e,n,h \<turnstile> (inline_call (Throw A) (fst (clearInitBlock e' xs)), snd (clearInitBlock e' xs)) \<leftrightarrow> (stk, loc, pc, \<lfloor>A\<rfloor>)"
  (is "\<lbrakk> _; _; _; _ \<rbrakk> \<Longrightarrow> ?concl e n e' xs pc stk loc")

  and bisims1_inline_calls_Throw:
  "\<lbrakk> P,es,n,h \<turnstile> (es', xs) [\<leftrightarrow>] (stk, loc, pc, None); calls es' = \<lfloor>(a, M, vs)\<rfloor>;
     compEs2 es ! pc = Invoke M (length vs); pc < length (compEs2 es) \<rbrakk>
  \<Longrightarrow> P,es,n,h \<turnstile> (inline_calls (Throw A) (fst (clearInitBlocks es' xs)), snd (clearInitBlocks es' xs)) [\<leftrightarrow>] (stk, loc, pc, \<lfloor>A\<rfloor>)"
  (is "\<lbrakk> _; _; _; _ \<rbrakk> \<Longrightarrow> ?concls es n es' xs pc stk loc")
proof(induct e n e' xs stk loc pc xcp\<equiv>"None :: addr option"
        and es n es' xs stk loc pc xcp\<equiv>"None :: addr option"
      rule: bisim1_bisims1_inducts_split)
  case (bisim1BinOp1 e1 n e' xs stk loc pc xcp e2 bop)
  note IH1 = `\<lbrakk>call e' = \<lfloor>(a, M, vs)\<rfloor>; compE2 e1 ! pc = Invoke M (length vs); pc < length (compE2 e1); xcp = None \<rbrakk>
              \<Longrightarrow> ?concl e1 n e' xs pc stk loc`
  note bisim1 = `P,e1,n,h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, xcp)`
  note ins = `compE2 (e1 \<guillemotleft>bop\<guillemotright> e2) ! pc = Invoke M (length vs)`
  note call = `call (e' \<guillemotleft>bop\<guillemotright> e2) = \<lfloor>(a, M, vs)\<rfloor>`
  show ?case
  proof(cases "is_val e'")
    case False
    with bisim1 call have "pc < length (compE2 e1)"
      by(auto intro: bisim1_call_pcD)
    with call ins IH1 `bsok e2 n` False `xcp = None` show ?thesis
      by(auto simp add: nth_append intro: bisim1_bisims1.bisim1BinOp1)
  next
    case True
    then obtain v where [simp]: "e' = Val v" by auto
    from bisim1 have "pc \<le> length (compE2 e1)" by(auto dest: bisim1_pc_length_compE2)
    moreover {
      assume pc: "pc < length (compE2 e1)"
      with bisim1 ins have False
	by(auto dest: bisim_Val_pc_not_Invoke simp add: nth_append) }
    ultimately have [simp]: "pc = length (compE2 e1)" by(cases "pc < length (compE2 e1)") auto
    from call ins show ?thesis by simp
  qed
next
  case bisim1BinOp2 thus ?case
    by(auto split: split_if_asm bop.split_asm dest: bisim1_bisims1.bisim1BinOp2)
next
  case (bisim1AAcc1 A n a' xs stk loc pc xcp i)
  note IH1 = `\<lbrakk>call a' = \<lfloor>(a, M, vs)\<rfloor>; compE2 A ! pc = Invoke M (length vs); pc < length (compE2 A); xcp = None \<rbrakk>
              \<Longrightarrow> ?concl A n a' xs pc stk loc`
  note bisim1 = `P,A,n,h \<turnstile> (a', xs) \<leftrightarrow> (stk, loc, pc, xcp)`
  note ins = `compE2 (A\<lfloor>i\<rceil>) ! pc = Invoke M (length vs)`
  note call = `call (a'\<lfloor>i\<rceil>) = \<lfloor>(a, M, vs)\<rfloor>`
  show ?case
  proof(cases "is_val a'")
    case False
    with bisim1 call have "pc < length (compE2 A)"
      by(auto intro: bisim1_call_pcD)
    with call ins IH1 `bsok i n` False `xcp = None` show ?thesis
      by(auto simp add: nth_append intro: bisim1_bisims1.bisim1AAcc1)
  next
    case True
    then obtain v where [simp]: "a' = Val v" by auto
    from bisim1 have "pc \<le> length (compE2 A)" by(auto dest: bisim1_pc_length_compE2)
    moreover {
      assume pc: "pc < length (compE2 A)"
      with bisim1 ins have False
	by(auto dest: bisim_Val_pc_not_Invoke simp add: nth_append) }
    ultimately have [simp]: "pc = length (compE2 A)" by(cases "pc < length (compE2 A)") auto
    from call ins show ?thesis by simp
  qed
next
  case bisim1AAcc2 thus ?case
    by(auto split: split_if_asm dest: bisim1_bisims1.bisim1AAcc2)
next
  case (bisim1AAss1 A n a' xs stk loc pc xcp i e)
  note IH1 = `\<lbrakk>call a' = \<lfloor>(a, M, vs)\<rfloor>; compE2 A ! pc = Invoke M (length vs); pc < length (compE2 A); xcp = None \<rbrakk>
              \<Longrightarrow> ?concl A n a' xs pc stk loc`
  note bisim1 = `P,A,n,h \<turnstile> (a', xs) \<leftrightarrow> (stk, loc, pc, xcp)`
  note ins = `compE2 (A\<lfloor>i\<rceil> := e) ! pc = Invoke M (length vs)`
  note call = `call (a'\<lfloor>i\<rceil> := e) = \<lfloor>(a, M, vs)\<rfloor>`
  show ?case
  proof(cases "is_val a'")
    case False
    with bisim1 call have "pc < length (compE2 A)"
      by(auto intro: bisim1_call_pcD)
    with call ins IH1 `bsok i n` `bsok e n` False `xcp = None` show ?thesis
      by(auto simp add: nth_append intro: bisim1_bisims1.bisim1AAss1)
  next
    case True
    then obtain v where [simp]: "a' = Val v" by auto
    from bisim1 have "pc \<le> length (compE2 A)" by(auto dest: bisim1_pc_length_compE2)
    moreover {
      assume pc: "pc < length (compE2 A)"
      with bisim1 ins have False
	by(auto dest: bisim_Val_pc_not_Invoke simp add: nth_append) }
    ultimately have [simp]: "pc = length (compE2 A)" by(cases "pc < length (compE2 A)") auto
    from call ins show ?thesis by simp
  qed
next
  case (bisim1AAss2 i n i' xs stk loc pc xcp A e v)
  note IH1 = `\<lbrakk>call i' = \<lfloor>(a, M, vs)\<rfloor>; compE2 i ! pc = Invoke M (length vs); pc < length (compE2 i); xcp = None \<rbrakk>
              \<Longrightarrow> ?concl i n i' xs pc stk loc`
  note bisim1 = `P,i,n,h \<turnstile> (i', xs) \<leftrightarrow> (stk, loc, pc, xcp)`
  note ins = `compE2 (A\<lfloor>i\<rceil> := e) ! (length (compE2 A) + pc) = Invoke M (length vs)`
  note call = `call (Val v\<lfloor>i'\<rceil> := e) = \<lfloor>(a, M, vs)\<rfloor>`
  show ?case
  proof(cases "is_val i'")
    case False
    with bisim1 call have "pc < length (compE2 i)"
      by(auto intro: bisim1_call_pcD)
    with call ins IH1 `bsok A n` `bsok e n` False `xcp = None` show ?thesis
      by(auto simp add: nth_append intro: bisim1_bisims1.bisim1AAss2)
  next
    case True
    then obtain v where [simp]: "i' = Val v" by auto
    from bisim1 have "pc \<le> length (compE2 i)" by(auto dest: bisim1_pc_length_compE2)
    moreover {
      assume pc: "pc < length (compE2 i)"
      with bisim1 ins have False
	by(auto dest: bisim_Val_pc_not_Invoke simp add: nth_append) }
    ultimately have [simp]: "pc = length (compE2 i)" by(cases "pc < length (compE2 i)") auto
    from call ins show ?thesis by simp
  qed
next
  case bisim1AAss3 thus ?case
    by(auto split: split_if_asm nat.split_asm simp add: nth_Cons dest: bisim1_bisims1.bisim1AAss3)
next
  case (bisim1FAss1 e n e' xs stk loc pc xcp e2 F D)
  note IH1 = `\<lbrakk>call e' = \<lfloor>(a, M, vs)\<rfloor>; compE2 e ! pc = Invoke M (length vs); pc < length (compE2 e); xcp = None \<rbrakk>
              \<Longrightarrow> ?concl e n e' xs pc stk loc`
  note bisim1 = `P,e,n,h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, xcp)`
  note ins = `compE2 (e\<bullet>F{D} := e2) ! pc = Invoke M (length vs)`
  note call = `call (e'\<bullet>F{D} := e2) = \<lfloor>(a, M, vs)\<rfloor>`
  show ?case
  proof(cases "is_val e'")
    case False
    with bisim1 call have "pc < length (compE2 e)"
      by(auto intro: bisim1_call_pcD)
    with call ins IH1 `bsok e2 n` False `xcp = None` show ?thesis
      by(auto simp add: nth_append intro: bisim1_bisims1.bisim1FAss1)
  next
    case True
    then obtain v where [simp]: "e' = Val v" by auto
    from bisim1 have "pc \<le> length (compE2 e)" by(auto dest: bisim1_pc_length_compE2)
    moreover {
      assume pc: "pc < length (compE2 e)"
      with bisim1 ins have False
	by(auto dest: bisim_Val_pc_not_Invoke simp add: nth_append) }
    ultimately have [simp]: "pc = length (compE2 e)" by(cases "pc < length (compE2 e)") auto
    from call ins show ?thesis by simp
  qed
next
  case bisim1FAss2 thus ?case
    by(auto split: split_if_asm nat.split_asm simp add: nth_Cons dest: bisim1_bisims1.bisim1FAss2)
next
  case (bisim1Call1 obj n obj' xs stk loc pc xcp ps M')
  note IH1 = `\<lbrakk>call obj' = \<lfloor>(a, M, vs)\<rfloor>; compE2 obj ! pc = Invoke M (length vs);
              pc < length (compE2 obj); xcp = None\<rbrakk>
              \<Longrightarrow> ?concl obj n obj' xs pc stk loc`
  note IH2 = `\<And>xs. \<lbrakk>calls ps = \<lfloor>(a, M, vs)\<rfloor>; compEs2 ps ! 0 = Invoke M (length vs); 0 < length (compEs2 ps); None = None\<rbrakk>
             \<Longrightarrow> ?concls ps n ps xs 0 [] xs`
  note ins = `compE2 (obj\<bullet>M'(ps)) ! pc = Invoke M (length vs)`
  note bisim1 = `P,obj,n,h \<turnstile> (obj', xs) \<leftrightarrow> (stk, loc, pc, xcp)`
  note xcp = `xcp = None`
  note call = `call (obj'\<bullet>M'(ps)) = \<lfloor>(a, M, vs)\<rfloor>`
  thus ?case
  proof(cases rule: call_callE)
    case CallObj
    with bisim1 call have "pc < length (compE2 obj)" by(auto intro: bisim1_call_pcD)
    with call ins CallObj IH1 `bsoks ps n` xcp show ?thesis
      by(auto intro: bisim1_bisims1.bisim1Call1)
  next
    case (CallParams v)
    from bisim1 have "pc \<le> length (compE2 obj)" by(auto dest: bisim1_pc_length_compE2)
    moreover {
      assume pc: "pc < length (compE2 obj)"
      with bisim1 ins CallParams have False by(auto dest: bisim_Val_pc_not_Invoke) }
    ultimately have [simp]: "pc = length (compE2 obj)" by(cases "pc < length (compE2 obj)") auto
    with bisim1 CallParams have [simp]: "stk = [v]" "loc = xs" by(auto dest: bisim1_Val_length_compE2D)
    from IH2[of loc] CallParams `bsoks ps n` `bsok obj n` ins
    show ?thesis
      apply(clarsimp simp add: compEs2_map_Val is_vals_conv split: split_if_asm)
      apply(drule bisim1_bisims1.bisim1CallParams)
      apply(auto simp add: neq_Nil_conv)
      done
  next
    case Call[simp]
    from bisim1 have "pc \<le> length (compE2 obj)" by(auto dest: bisim1_pc_length_compE2)
    moreover {
      assume pc: "pc < length (compE2 obj)"
      with bisim1 ins have False by(auto dest: bisim_Val_pc_not_Invoke simp add: nth_append) }
    ultimately have [simp]: "pc = length (compE2 obj)" by(cases "pc < length (compE2 obj)") auto
    with ins have [simp]: "vs = []" by(auto simp add: nth_append compEs2_map_Val split: split_if_asm)
    from bisim1 have [simp]: "stk = [Addr a]" "xs = loc" by(auto dest: bisim1_Val_length_compE2D)
    from `bsok obj n` show ?thesis by(auto intro: bisim1CallThrow[of "[]" "[]", simplified])
  qed
next
  case (bisim1CallParams ps n ps' xs stk loc pc xcp obj M' v)
  note IH2 = `\<lbrakk>calls ps' = \<lfloor>(a, M, vs)\<rfloor>; compEs2 ps ! pc = Invoke M (length vs); pc < length (compEs2 ps); xcp = None\<rbrakk>
             \<Longrightarrow> ?concls ps n ps' xs pc stk loc`
  note ins = `compE2 (obj\<bullet>M'(ps)) ! (length (compE2 obj) + pc) = Invoke M (length vs)`
  note bisim2 = `P,ps,n,h \<turnstile> (ps', xs) [\<leftrightarrow>] (stk, loc, pc, xcp)`
  note xcp = `xcp = None`
  note call = `call (Val v\<bullet>M'(ps')) = \<lfloor>(a, M, vs)\<rfloor>`
  thus ?case
  proof(cases rule: call_callE)
    case CallObj thus ?thesis by simp
  next
    case (CallParams v')
    hence [simp]: "v' = v" and call': "calls ps' = \<lfloor>(a, M, vs)\<rfloor>" by auto
    from bisim2 call' have "pc < length (compEs2 ps)" by(auto intro: bisims1_calls_pcD)
    with IH2 CallParams `bsok obj n` xcp ins show ?thesis
      by(auto simp add: is_vals_conv split: split_if_asm intro: bisim1_bisims1.bisim1CallParams)
  next
    case Call
    hence [simp]: "v = Addr a" "M' = M" "ps' = map Val vs" by auto
    from bisim2 have "pc \<le> length (compEs2 ps)" by(auto dest: bisims1_pc_length_compEs2)
    moreover {
      assume pc: "pc < length (compEs2 ps)"
      with bisim2 ins have False by(auto dest: bisims_Val_pc_not_Invoke simp add: nth_append) }
    ultimately have [simp]: "pc = length (compEs2 ps)" by(cases "pc < length (compEs2 ps)") auto
    from bisim2 have [simp]: "stk = rev vs" "xs = loc" by(auto dest: bisims1_Val_length_compEs2D)
    from bisim2 have "length ps = length vs" by(auto dest: bisims1_lengthD)
    with `bsoks ps n` `bsok obj n` show ?thesis by(auto intro: bisim1CallThrow)
  qed
next
  case (bisims1List1 e n e' xs stk loc pc xcp es)
  note IH1 = `\<lbrakk>call e' = \<lfloor>(a, M, vs)\<rfloor>; compE2 e ! pc = Invoke M (length vs); pc < length (compE2 e); xcp = None\<rbrakk>
              \<Longrightarrow> ?concl e n e' xs pc stk loc`
  note IH2 = `\<And>xs. \<lbrakk>calls es = \<lfloor>(a, M, vs)\<rfloor>; compEs2 es ! 0 = Invoke M (length vs); 0 < length (compEs2 es); None = None\<rbrakk>
             \<Longrightarrow> ?concls es n es xs 0 [] xs`
  note bisim1 = `P,e,n,h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, xcp)`
  note call = `calls (e' # es) = \<lfloor>(a, M, vs)\<rfloor>`
  note ins = `compEs2 (e # es) ! pc = Invoke M (length vs)`
  show ?case
  proof(cases "is_val e'")
    case False
    with bisim1 call have "pc < length (compE2 e)" by(auto intro: bisim1_call_pcD)
    with call ins False IH1 `bsoks es n` `xcp = None` show ?thesis
      by(auto simp add: nth_append split_beta intro: bisim1_bisims1.bisims1List1)
  next
    case True
    then obtain v where [simp]: "e' = Val v" by auto
    from bisim1 have "pc \<le> length (compE2 e)" by(auto dest: bisim1_pc_length_compE2)
    moreover {
      assume pc: "pc < length (compE2 e)"
      with bisim1 ins have False by(auto dest: bisim_Val_pc_not_Invoke simp add: nth_append) }
    ultimately have [simp]: "pc = length (compE2 e)" by(cases "pc < length (compE2 e)") auto
    with bisim1 have [simp]: "stk = [v]" "loc = xs" by(auto dest: bisim1_Val_length_compE2D)
    from call have "es \<noteq> []" by(cases es) simp_all
    with IH2[of loc] call `bsoks es n` `bsok e n` ins
    show ?thesis by(auto split: split_if_asm dest: bisims1List2)
  qed
qed(auto split: split_if_asm bop.split_asm intro: bisim1_bisims1.intros dest: bisim1_pc_length_compE2)

lemma \<tau>Red1_preserves_sconf:
  assumes wf: "wf_prog wf_md P" and hconf: "P \<turnstile> h \<surd>"
  and exsconf: "exsconf P h T (e, xs)" and red: "\<tau>Red P h e xs e' xs'"
  shows "exsconf P h T (e', xs')"
using red exsconf
by (induct)(auto intro: red1_preserves_exsconf[OF wf hconf])

lemma bisim1_max_stack: "P,e,n,h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, xcp) \<Longrightarrow> length stk \<le> max_stack e"
  and bisims1_max_stacks: "P,es,n,h \<turnstile> (es', xs) [\<leftrightarrow>] (stk, loc, pc, xcp) \<Longrightarrow> length stk \<le> max_stacks es"
apply(induct rule: bisim1_bisims1_inducts_split)
apply(auto simp add: max_stack1[simplified] max_def max_stacks_ge_length)
apply(drule sym, simp add: max_stacks_ge_length, drule sym, simp, rule le_trans[OF max_stacks_ge_length], simp)
done

inductive bisim1_list :: "J1_prog \<Rightarrow> heap \<Rightarrow> cname \<Rightarrow> mname \<Rightarrow> nat \<Rightarrow> (expr1 \<times> locals1) list \<Rightarrow> frame list \<Rightarrow> bool"
  for P:: J1_prog and h :: heap
  where
  bl1_Nil: "length vs = pns \<Longrightarrow> bisim1_list P h C M pns [(addr a\<bullet>M(map Val vs), xs)] []"

| bl1_Cons:
  "\<lbrakk> bisim1_list P h C M (length Ts) exs frs;
     P \<turnstile> C sees M : Ts\<rightarrow>T = body in D; 
     P,blocks1 (Suc 0) Ts body,Suc 0,h \<turnstile> ex \<leftrightarrow> (rev vs' @ Addr a # stk, loc, pc, None);
     call (fst ex) = \<lfloor>(a, M', vs')\<rfloor>;
     h a = \<lfloor>Obj C'' fs\<rfloor>;
     P \<turnstile> C'' sees M' : Ts'\<rightarrow>T''=meth in C';
     compE2 body ! pc = Invoke M' (length vs');
     exsconf P h T ex \<rbrakk>
  \<Longrightarrow> bisim1_list P h C' M' (length vs') (ex # exs) ((rev vs' @ Addr a # stk,loc,C,M,pc) # frs)"


inductive bisim1_list1 :: "J1_prog \<Rightarrow> heap \<Rightarrow> expr1 \<times> locals1 \<Rightarrow> (expr1 \<times> locals1) list \<Rightarrow> addr option \<Rightarrow> frame list \<Rightarrow> bool"
  for P:: J1_prog and h :: heap
  where

  bl1_Normal:
  "\<lbrakk> bisim1_list P h C M (length Ts) exs frs;
     P \<turnstile> C sees M : Ts \<rightarrow> T = body in D;
     P,blocks1 (Suc 0) Ts body,Suc 0, h \<turnstile> ex \<leftrightarrow> (stk, loc, pc, xcp);
     exsconf P h T ex; 
     P \<turnstile> h \<surd> \<rbrakk>
  \<Longrightarrow> bisim1_list1 P h ex exs xcp ((stk, loc, C, M, pc) # frs)"

| bl1_finalVal:
  "P \<turnstile> h \<surd> \<Longrightarrow> bisim1_list1 P h (Val v, xs) [] None []"

| bl1_finalThrow:
  "P \<turnstile> h \<surd> \<Longrightarrow> bisim1_list1 P h (Throw a, xs) [] \<lfloor>a\<rfloor> []"

inductive_cases bl1_cases [elim!]:
 "bisim1_list P h C M pns [] frs"
 "bisim1_list P h C M pns (ex # exs) frs"
 "bisim1_list P h C M pns exs (f # frs)"

lemma bisim1_list_hext_mono:
  assumes major: "bisim1_list P h C M pns exs frs"
  and hext: "hext h h'"
  shows "bisim1_list P h' C M pns exs frs"
using major
proof(induct rule: bisim1_list.induct)
  case bl1_Nil thus ?case by(rule bisim1_list.bl1_Nil)
next
  case (bl1_Cons C M Ts exs frs T body D ex vs' a stk loc pc M' C'' fs Ts' T'' meth C')
  from `P,blocks1 (Suc 0) Ts body,Suc 0,h \<turnstile> ex \<leftrightarrow> (rev vs' @ Addr a # stk, loc, pc, None)` hext
  have "P,blocks1 (Suc 0) Ts body,Suc 0,h' \<turnstile> ex \<leftrightarrow> (rev vs' @ Addr a # stk, loc, pc, None)" by(rule bisim1_hext_mono)
  moreover from `h a = \<lfloor>Obj C'' fs\<rfloor>` hext obtain fs' where "h' a = \<lfloor>Obj C'' fs'\<rfloor>" by(auto dest: hext_objD)
  moreover from `exsconf P h T ex` hext have "exsconf P h' T ex" by(rule exsconf_hext_mono)
  ultimately show ?case using bl1_Cons by-(rule bisim1_list.bl1_Cons)
qed

lemma bisim1_max_vars: "P,E,n,h \<turnstile> (e, xs) \<leftrightarrow> (stk, loc, pc, xcp) \<Longrightarrow> max_vars E \<ge> max_vars e"
  and bisims1_max_varss: "P,Es,n,h \<turnstile> (es,xs) [\<leftrightarrow>] (stk,loc,pc,xcp) \<Longrightarrow> max_varss Es \<ge> max_varss es"
apply(induct rule: bisim1_bisims1_inducts_split)
apply(auto)
done

lemma WT1_ex_simp: "P,E \<turnstile>1 e :: T \<Longrightarrow> \<exists>T E. P,E \<turnstile>1 e :: T" by blast

lemma noRetBlocks_map_Val [simp]: "noRetBlocks (map Val vs)"
by(induct vs) auto

lemma bisim1_call_\<tau>Exec_move:
  "\<lbrakk> P,e,n,h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, None); call e' = \<lfloor>(a, M', vs)\<rfloor>; n + max_vars e' \<le> length xs; \<exists>T E. P,E \<turnstile>1 e :: T \<rbrakk>
  \<Longrightarrow> \<exists>pc' loc' stk'. \<tau>Exec_move P e h (stk, loc, pc, None) (rev vs @ Addr a # stk', loc', pc', None) \<and>
                     pc' < length (compE2 e) \<and> compE2 e ! pc' = Invoke M' (length vs) \<and>
                     P,e,n,h \<turnstile> clearInitBlock e' xs \<leftrightarrow> (rev vs @ Addr a # stk', loc', pc', None)"
  (is "\<lbrakk> _; _; _; ?wt e \<rbrakk> \<Longrightarrow> ?concl e n e' xs pc stk loc")

  and bisims1_calls_\<tau>Exec_moves:
  "\<lbrakk> P,es,n,h \<turnstile> (es',xs) [\<leftrightarrow>] (stk, loc, pc, None); calls es' = \<lfloor>(a, M', vs)\<rfloor>;
     n + max_varss es' \<le> length xs; \<exists>Ts E. P,E \<turnstile>1 es [::] Ts \<rbrakk>
  \<Longrightarrow> \<exists>pc' stk' loc'. \<tau>Exec_moves P es h (stk, loc, pc, None) (rev vs @ Addr a # stk', loc', pc', None) \<and>
                     pc' < length (compEs2 es) \<and> compEs2 es ! pc' = Invoke M' (length vs) \<and>
                     P,es,n,h \<turnstile> clearInitBlocks es' xs [\<leftrightarrow>] (rev vs @ Addr a # stk', loc', pc', None)"
  (is "\<lbrakk>_; _; _; ?wts es \<rbrakk> \<Longrightarrow> ?concls es n es' xs pc stk loc")
proof(induct e n e' xs stk loc pc xcp\<equiv>"None :: addr option" and es n es' xs stk loc pc xcp\<equiv>"None :: addr option"
            rule: bisim1_bisims1_inducts_split)
  case bisim1Val2 thus ?case by auto
next
  case bisim1New thus ?case by auto
next
  case bisim1NewThrow thus ?case by auto
next
  case bisim1NewArray thus ?case
    by(auto simp add: WT1_ex_simp)(fastsimp intro: bisim1_bisims1.bisim1NewArray intro!: exI)
next
  case bisim1NewArrayNegative thus ?case by auto
next
  case bisim1NewArrayFail thus ?case by auto
next
  case bisim1NewArrayThrow thus ?case by auto
next
  case bisim1Cast thus ?case
    by(auto simp add: WT1_ex_simp)(fastsimp intro: bisim1_bisims1.bisim1Cast intro!: exI)+
next
  case bisim1CastFail thus ?case by auto
next
  case bisim1CastThrow thus ?case by auto
next
  case bisim1Val thus ?case by auto
next
  case bisim1Var thus ?case by auto
next
  case (bisim1BinOp1 e1 n e' xs stk loc pc xcp e2 bop)
  note IH1 = `\<lbrakk>call e' = \<lfloor>(a, M', vs)\<rfloor>; n + max_vars e' \<le> length xs; ?wt e1; xcp = None\<rbrakk> \<Longrightarrow> ?concl e1 n e' xs pc stk loc`
  note IH2 = `\<And>xs. \<lbrakk>call e2 = \<lfloor>(a, M', vs)\<rfloor>; n + max_vars e2 \<le> length xs; ?wt e2; None = None\<rbrakk> \<Longrightarrow> ?concl e2 n e2 xs 0 [] xs`
  note call = `call (e' \<guillemotleft>bop\<guillemotright> e2) = \<lfloor>(a, M', vs)\<rfloor>`
  note len = `n + max_vars (e' \<guillemotleft>bop\<guillemotright> e2) \<le> length xs`
  note xcp = `xcp = None`
  from `?wt (e1 \<guillemotleft>bop\<guillemotright> e2)` obtain E T1 T2 where wt1: "P,E \<turnstile>1 e1 :: T1" and wt2: "P,E \<turnstile>1 e2 :: T2" by auto
  note bisim1 = `P,e1,n,h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, xcp)`
  show ?case
  proof(cases "is_val e'")
    case True
    then obtain v where [simp]: "e' = Val v" by auto
    from bisim1 wt1 have "\<tau>Exec_move P e1 h (stk, loc, pc, None) ([v], loc, length (compE2 e1), None)"
      and [simp]: "xs = loc" by(auto dest!: bisim1Val2D1)
    hence "\<tau>Exec_move P (e1\<guillemotleft>bop\<guillemotright>e2) h (stk, loc, pc, None) ([v], loc, length (compE2 e1), None)"
      by-(rule BinOp_\<tau>Exec_meth_xt1)
    also from call IH2[of loc] len wt2 obtain pc' stk' loc'
      where exec: "\<tau>Exec_move P e2 h ([], xs, 0, None) (rev vs @ Addr a # stk', loc', pc', None)"
      and ins: "compE2 e2 ! pc' = Invoke M' (length vs)" "pc' < length (compE2 e2)"
      and bisim': "P,e2,n,h \<turnstile> clearInitBlock e2 xs \<leftrightarrow> (rev vs @ Addr a # stk', loc', pc', None)" by auto
    from BinOp_\<tau>Exec_meth_xt2[OF exec, of e1 bop v]
    have "\<tau>Exec_move P (e1\<guillemotleft>bop\<guillemotright>e2) h ([v], loc, length (compE2 e1), None) (rev vs @ Addr a # (stk' @ [v]), loc', length (compE2 e1) + pc', None)" by simp
    also from bisim' `bsok e1 n`
    have "P,e1\<guillemotleft>bop\<guillemotright>e2,n,h \<turnstile> (Val v \<guillemotleft>bop\<guillemotright> fst (clearInitBlock e2 xs), snd (clearInitBlock e2 xs)) \<leftrightarrow> ((rev vs @ Addr a # stk') @ [v], loc', length (compE2 e1) + pc', None)"
      by -(rule bisim1BinOp2, simp)
    ultimately show ?thesis using ins by fastsimp
  next
    case False with IH1 wt1 len `bsok e2 n` False xcp call show ?thesis
      by(clarsimp simp add: WT1_ex_simp)(fastsimp intro: bisim1_bisims1.bisim1BinOp1 intro!: exI)
  qed
next
  case (bisim1BinOp2 e2 n e' xs stk loc pc xcp e1 bop v1)
  then obtain pc' loc' stk' where pc': "pc' < length (compE2 e2)" "compE2 e2 ! pc' = Invoke M' (length vs)"
    and exec: "\<tau>Exec_move P e2 h (stk, loc, pc, None) (rev vs @ Addr a # stk', loc', pc', None)"
    and bisim': "P,e2,n,h \<turnstile> clearInitBlock e' xs \<leftrightarrow> (rev vs @ Addr a # stk', loc', pc', None)" by fastsimp
  from exec have "\<tau>Exec_move P (e1 \<guillemotleft>bop\<guillemotright> e2) h (stk @ [v1], loc, length (compE2 e1) + pc, None)
                                              ((rev vs @ Addr a # stk') @ [v1], loc', length (compE2 e1) + pc', None)"
    by(rule BinOp_\<tau>Exec_meth_xt2)
  moreover from bisim' `bsok e1 n`
  have "P,e1 \<guillemotleft>bop\<guillemotright> e2,n,h \<turnstile> (Val v1 \<guillemotleft>bop\<guillemotright> fst (clearInitBlock e' xs), snd (clearInitBlock e' xs)) \<leftrightarrow> ((rev vs @ Addr a # stk') @ [v1], loc', length (compE2 e1) + pc', None)"
    by -(rule bisim1_bisims1.bisim1BinOp2, simp)
  ultimately show ?case using pc' by(fastsimp)
next
  case bisim1BinOpThrow1 thus ?case by simp
next
  case bisim1BinOpThrow2 thus ?case by simp
next
  case bisim1LAss1 thus ?case
    by(auto simp add: WT1_ex_simp)(fastsimp intro: bisim1_bisims1.bisim1LAss1 intro!: exI)
next
  case bisim1LAss2 thus ?case by simp
next
  case bisim1LAssThrow thus ?case by simp
next
  case (bisim1AAcc1 A n a' xs stk loc pc xcp i)
  note IH1 = `\<lbrakk>call a' = \<lfloor>(a, M', vs)\<rfloor>; n + max_vars a' \<le> length xs; ?wt A; xcp = None\<rbrakk> \<Longrightarrow> ?concl A n a' xs pc stk loc`
  note IH2 = `\<And>xs. \<lbrakk>call i = \<lfloor>(a, M', vs)\<rfloor>; n + max_vars i \<le> length xs; ?wt i; None = None\<rbrakk> \<Longrightarrow> ?concl i n i xs 0 [] xs`
  note call = `call (a'\<lfloor>i\<rceil>) = \<lfloor>(a, M', vs)\<rfloor>`
  note len = `n + max_vars (a'\<lfloor>i\<rceil>) \<le> length xs`
  note xcp = `xcp = None`
  from `?wt (A\<lfloor>i\<rceil>)` obtain E T1 T2 where wt1: "P,E \<turnstile>1 A :: T1" and wt2: "P,E \<turnstile>1 i :: T2" by auto
  note bisim1 = `P,A,n,h \<turnstile> (a', xs) \<leftrightarrow> (stk, loc, pc, xcp)`
  show ?case
  proof(cases "is_val a'")
    case True
    then obtain v where [simp]: "a' = Val v" by auto
    from bisim1 wt1 have "\<tau>Exec_move P A h (stk, loc, pc, None) ([v], loc, length (compE2 A), None)"
      and [simp]: "xs = loc" by(auto dest!: bisim1Val2D1)
    hence "\<tau>Exec_move P (A\<lfloor>i\<rceil>) h (stk, loc, pc, None) ([v], loc, length (compE2 A), None)"
      by-(rule AAcc_\<tau>Exec_meth_xt1)
    also from call IH2[of loc] len wt2 obtain pc' stk' loc'
      where exec: "\<tau>Exec_move P i h ([], xs, 0, None) (rev vs @ Addr a # stk', loc', pc', None)"
      and ins: "compE2 i ! pc' = Invoke M' (length vs)" "pc' < length (compE2 i)"
      and bisim': "P,i,n,h \<turnstile> clearInitBlock i xs \<leftrightarrow> (rev vs @ Addr a # stk', loc', pc', None)" by auto
    from AAcc_\<tau>Exec_meth_xt2[OF exec, of A v]
    have "\<tau>Exec_move P (A\<lfloor>i\<rceil>) h ([v], loc, length (compE2 A), None) (rev vs @ Addr a # (stk' @ [v]), loc', length (compE2 A) + pc', None)" by simp
    also from bisim' `bsok A n`
    have "P,A\<lfloor>i\<rceil>,n,h \<turnstile> (Val v\<lfloor>fst (clearInitBlock i xs)\<rceil>, snd (clearInitBlock i xs)) \<leftrightarrow> ((rev vs @ Addr a # stk') @ [v], loc', length (compE2 A) + pc', None)"
      by - (rule bisim1AAcc2, simp)
    ultimately show ?thesis using ins by fastsimp
  next
    case False with IH1 wt1 len `bsok i n` False xcp call show ?thesis
      by(clarsimp simp add: WT1_ex_simp)(fastsimp intro: bisim1_bisims1.bisim1AAcc1 intro!: exI)
  qed
next
  case (bisim1AAcc2 i n i' xs stk loc pc xcp A v)
  then obtain pc' loc' stk' where pc': "pc' < length (compE2 i)" "compE2 i ! pc' = Invoke M' (length vs)"
    and exec: "\<tau>Exec_move P i h (stk, loc, pc, None) (rev vs @ Addr a # stk', loc', pc', None)"
    and bisim': "P,i,n,h \<turnstile> clearInitBlock i' xs \<leftrightarrow> (rev vs @ Addr a # stk', loc', pc', None)" by fastsimp
  from exec have "\<tau>Exec_move P (A\<lfloor>i\<rceil>) h (stk @ [v], loc, length (compE2 A) + pc, None)
                                       ((rev vs @ Addr a # stk') @ [v], loc', length (compE2 A) + pc', None)"
    by(rule AAcc_\<tau>Exec_meth_xt2)
  moreover from bisim' `bsok A n`
  have "P,A\<lfloor>i\<rceil>,n,h \<turnstile> (Val v\<lfloor>fst (clearInitBlock i' xs)\<rceil>, snd (clearInitBlock i' xs)) \<leftrightarrow> ((rev vs @ Addr a # stk') @ [v], loc', length (compE2 A) + pc', None)"
    by -(rule bisim1_bisims1.bisim1AAcc2, simp)
  ultimately show ?case using pc' by(fastsimp)
next
  case bisim1AAccThrow1 thus ?case by simp
next
  case bisim1AAccThrow2 thus ?case by simp
next
  case bisim1AAccNull thus ?case by simp
next
  case bisim1AAccBounds thus ?case by simp
next
  case (bisim1AAss1 A n a' xs stk loc pc xcp i e)
  note IH1 = `\<lbrakk>call a' = \<lfloor>(a, M', vs)\<rfloor>; n + max_vars a' \<le> length xs; ?wt A; xcp = None\<rbrakk> \<Longrightarrow> ?concl A n a' xs pc stk loc`
  note IH2 = `\<And>xs. \<lbrakk>call i = \<lfloor>(a, M', vs)\<rfloor>; n + max_vars i \<le> length xs; ?wt i; None = None\<rbrakk> \<Longrightarrow> ?concl i n i xs 0 [] xs`
  note IH3 = `\<And>xs. \<lbrakk>call e = \<lfloor>(a, M', vs)\<rfloor>; n + max_vars e \<le> length xs; ?wt e; None = None\<rbrakk> \<Longrightarrow> ?concl e n e xs 0 [] xs`
  note call = `call (a'\<lfloor>i\<rceil> := e) = \<lfloor>(a, M', vs)\<rfloor>`
  note len = `n + max_vars (a'\<lfloor>i\<rceil> := e) \<le> length xs`
  note xcp = `xcp = None`
  from `?wt (A\<lfloor>i\<rceil> := e)` obtain E T1 T3 where wt1: "P,E \<turnstile>1 A :: T1"
    and wt2: "P,E \<turnstile>1 i :: Integer" and wt3: "P,E \<turnstile>1 e :: T3" by auto
  note bisim1 = `P,A,n,h \<turnstile> (a', xs) \<leftrightarrow> (stk, loc, pc, xcp)`
  note bisim2 = `P,i,n,h \<turnstile> (i, loc) \<leftrightarrow> ([], loc, 0, None)`
  show ?case
  proof(cases "is_val a'")
    case True
    then obtain v where [simp]: "a' = Val v" by auto
    from bisim1 wt1 have "\<tau>Exec_move P A h (stk, loc, pc, None) ([v], loc, length (compE2 A), None)"
      and [simp]: "xs = loc" by(auto dest!: bisim1Val2D1)
    hence exec: "\<tau>Exec_move P (A\<lfloor>i\<rceil> := e) h (stk, loc, pc, None) ([v], loc, length (compE2 A), None)"
      by-(rule AAss_\<tau>Exec_meth_xt1)
    show ?thesis
    proof(cases "is_val i")
      case True
      then obtain v' where [simp]: "i = Val v'" by auto
      note exec also from bisim2 wt2
      have "\<tau>Exec_move P i h ([], loc, 0, None) ([v'], loc, length (compE2 i), None)"
	by(auto dest!: bisim1Val2D1)
      from AAss_\<tau>Exec_meth_xt2[OF this, of A e v]
      have "\<tau>Exec_move P (A\<lfloor>i\<rceil> := e) h ([v], loc, length (compE2 A), None) ([v', v], loc, length (compE2 A) + length (compE2 i), None)" by simp
      also from call IH3[of loc] len wt3 obtain pc' stk' loc'
      where exec: "\<tau>Exec_move P e h ([], loc, 0, None) (rev vs @ Addr a # stk', loc', pc', None)"
      and ins: "compE2 e ! pc' = Invoke M' (length vs)" "pc' < length (compE2 e)"
      and bisim': "P,e,n,h \<turnstile> clearInitBlock e loc \<leftrightarrow> (rev vs @ Addr a # stk', loc', pc', None)" by auto
      from AAss_\<tau>Exec_meth_xt3[OF exec, of A i v' v]
      have "\<tau>Exec_move P (A\<lfloor>i\<rceil> := e) h ([v', v], loc, length (compE2 A) + length (compE2 i), None)
	                ((rev vs @ Addr a # stk') @ [v', v], loc', length (compE2 A) + length (compE2 i) + pc', None)" by simp
      also from bisim' `bsok A n` `bsok i n`
      have "P,A\<lfloor>i\<rceil> := e,n,h \<turnstile> (Val v\<lfloor>Val v'\<rceil> := fst (clearInitBlock e xs), snd (clearInitBlock e xs)) \<leftrightarrow> ((rev vs @ Addr a # stk') @ [v', v], loc', length (compE2 A) + length (compE2 i) + pc', None)"
	by - (rule bisim1AAss3, simp)
      ultimately show ?thesis using ins by fastsimp
    next
      case False
      note exec also from False call IH2[of loc] len wt2 obtain pc' stk' loc'
	where exec: "\<tau>Exec_move P i h ([], xs, 0, None) (rev vs @ Addr a # stk', loc', pc', None)"
	and ins: "compE2 i ! pc' = Invoke M' (length vs)" "pc' < length (compE2 i)"
	and bisim': "P,i,n,h \<turnstile> clearInitBlock i xs \<leftrightarrow> (rev vs @ Addr a # stk', loc', pc', None)" by auto
      from AAss_\<tau>Exec_meth_xt2[OF exec, of A e v]
      have "\<tau>Exec_move P (A\<lfloor>i\<rceil> := e) h ([v], loc, length (compE2 A), None) (rev vs @ Addr a # (stk' @ [v]), loc', length (compE2 A) + pc', None)" by simp
      also from bisim' `bsok A n` `bsok e n`
      have "P,A\<lfloor>i\<rceil> := e,n,h \<turnstile> (Val v\<lfloor>fst (clearInitBlock i xs)\<rceil> := e, snd (clearInitBlock i xs)) \<leftrightarrow> ((rev vs @ Addr a # stk') @ [v], loc', length (compE2 A) + pc', None)"
	by - (rule bisim1AAss2, simp)
      ultimately show ?thesis using ins False by(fastsimp intro!: exI)
    qed
  next
    case False with IH1 wt1 len `bsok i n` `bsok e n` False xcp call show ?thesis
      by(clarsimp simp add: WT1_ex_simp)(fastsimp intro: bisim1_bisims1.bisim1AAss1 intro!: exI)
  qed
next
  case (bisim1AAss2 i n i' xs stk loc pc xcp A e v)
  note IH2 = `\<lbrakk>call i' = \<lfloor>(a, M', vs)\<rfloor>; n + max_vars i' \<le> length xs; ?wt i; xcp = None\<rbrakk> \<Longrightarrow> ?concl i n i' xs pc stk loc`
  note IH3 = `\<And>xs. \<lbrakk>call e = \<lfloor>(a, M', vs)\<rfloor>; n + max_vars e \<le> length xs; ?wt e; None = None\<rbrakk> \<Longrightarrow> ?concl e n e xs 0 [] xs`
  note call = `call (Val v\<lfloor>i'\<rceil> := e) = \<lfloor>(a, M', vs)\<rfloor>`
  note len = `n + max_vars (Val v\<lfloor>i'\<rceil> := e) \<le> length xs`
  note xcp = `xcp = None`
  from `?wt (A\<lfloor>i\<rceil> := e)` obtain E T3 where wt2: "P,E \<turnstile>1 i :: Integer" and wt3: "P,E \<turnstile>1 e :: T3" by auto
  note bisim2 = `P,i,n,h \<turnstile> (i', xs) \<leftrightarrow> (stk, loc, pc, xcp)`
  show ?case
  proof(cases "is_val i'")
    case True
    then obtain v' where [simp]: "i' = Val v'" by auto
    from bisim2 wt2 have exec: "\<tau>Exec_move P i h (stk, loc, pc, None) ([v'], loc, length (compE2 i), None)"
      and [simp]: "xs = loc" by(auto dest!: bisim1Val2D1)
    from AAss_\<tau>Exec_meth_xt2[OF exec, of A e v]
    have "\<tau>Exec_move P (A\<lfloor>i\<rceil> := e) h (stk @ [v], loc, length (compE2 A) + pc, None) ([v', v], loc, length (compE2 A) + length (compE2 i), None)" by simp
    also from call IH3[of loc] len wt3 obtain pc' stk' loc'
      where exec: "\<tau>Exec_move P e h ([], xs, 0, None) (rev vs @ Addr a # stk', loc', pc', None)"
      and ins: "compE2 e ! pc' = Invoke M' (length vs)" "pc' < length (compE2 e)"
      and bisim': "P,e,n,h \<turnstile> clearInitBlock e xs \<leftrightarrow> (rev vs @ Addr a # stk', loc', pc', None)" by auto
    from AAss_\<tau>Exec_meth_xt3[OF exec, of A i v' v]
    have "\<tau>Exec_move P (A\<lfloor>i\<rceil> := e) h ([v', v], loc, length (compE2 A) + length (compE2 i), None)
                       ((rev vs @ Addr a # stk') @ [v', v], loc', length (compE2 A) + length (compE2 i) + pc', None)" by simp
    also from bisim' `bsok A n` `bsok i n`
    have "P,A\<lfloor>i\<rceil> := e,n,h \<turnstile> (Val v\<lfloor>Val v'\<rceil> := fst (clearInitBlock e xs), snd (clearInitBlock e xs)) \<leftrightarrow> ((rev vs @ Addr a # stk') @ [v', v], loc', length (compE2 A) + length (compE2 i) + pc', None)"
      by -(rule bisim1AAss3, simp)
    ultimately show ?thesis using ins by(fastsimp intro!: exI)
  next
    case False
    with IH2 wt2 len xcp call obtain pc' loc' stk'
      where ins: "pc' < length (compE2 i)" "compE2 i ! pc' = Invoke M' (length vs)"
      and exec: "\<tau>Exec_move P i h (stk, loc, pc, None) (rev vs @ Addr a # stk', loc', pc', None)"
      and bisim': "P,i,n,h \<turnstile> clearInitBlock i' xs \<leftrightarrow> (rev vs @ Addr a # stk', loc', pc', None)" by fastsimp
    from bisim' `bsok A n` `bsok e n` have "P,A\<lfloor>i\<rceil> := e,n,h \<turnstile> (Val v\<lfloor>fst (clearInitBlock i' xs)\<rceil> := e, snd (clearInitBlock i' xs)) \<leftrightarrow> ((rev vs @ Addr a # stk') @ [v], loc', length (compE2 A) + pc', None)"
      by -(rule bisim1_bisims1.bisim1AAss2, simp)
    with AAss_\<tau>Exec_meth_xt2[OF exec, of A e v] ins False show ?thesis by(auto intro!: exI)
  qed
next
  case (bisim1AAss3 e n e' xs stk loc pc xcp A i v v')
  then obtain pc' loc' stk' where pc': "pc' < length (compE2 e)" "compE2 e ! pc' = Invoke M' (length vs)"
    and exec: "\<tau>Exec_move P e h (stk, loc, pc, None) (rev vs @ Addr a # stk', loc', pc', None)"
    and bisim': "P,e,n,h \<turnstile> clearInitBlock e' xs \<leftrightarrow> (rev vs @ Addr a # stk', loc', pc', None)" by fastsimp
  from exec have "\<tau>Exec_move P (A\<lfloor>i\<rceil>:=e) h (stk @ [v', v], loc, length (compE2 A) + length (compE2 i) + pc, None)
                                       ((rev vs @ Addr a # stk') @ [v', v], loc', length (compE2 A) + length (compE2 i) + pc', None)"
    by(rule AAss_\<tau>Exec_meth_xt3)
  moreover from bisim' `bsok A n` `bsok i n`
  have "P,A\<lfloor>i\<rceil> := e,n,h \<turnstile> (Val v\<lfloor>Val v'\<rceil> := fst (clearInitBlock e' xs), snd (clearInitBlock e' xs)) \<leftrightarrow> ((rev vs @ Addr a # stk') @ [v', v], loc', length (compE2 A) + length (compE2 i) + pc', None)"
    by -(rule bisim1_bisims1.bisim1AAss3, simp)
  ultimately show ?case using pc' by(fastsimp intro!: exI)
next
  case bisim1AAssThrow1 thus ?case by simp
next
  case bisim1AAssThrow2 thus ?case by simp
next
  case bisim1AAssThrow3 thus ?case by simp
next
  case bisim1AAssNull thus ?case by simp
next
  case bisim1AAssBounds thus ?case by simp
next
  case bisim1AAssStore thus ?case by simp
next
  case bisim1AAss4 thus ?case by simp
next
  case bisim1ALength thus ?case
    by(auto simp add: WT1_ex_simp)(fastsimp intro: bisim1_bisims1.bisim1ALength intro!: exI)
next
  case bisim1ALengthNull thus ?case by simp
next
  case bisim1ALengthThrow thus ?case by simp
next
  case bisim1FAcc thus ?case
    by(auto simp add: WT1_ex_simp)(fastsimp intro: bisim1_bisims1.bisim1FAcc intro!: exI)
next
  case bisim1FAccNull thus ?case by simp
next
  case bisim1FAccThrow thus ?case by simp
next
  case (bisim1FAss1 e n e' xs stk loc pc xcp e2 F D)
  note IH1 = `\<lbrakk>call e' = \<lfloor>(a, M', vs)\<rfloor>; n + max_vars e' \<le> length xs; ?wt e; xcp = None\<rbrakk> \<Longrightarrow> ?concl e n e' xs pc stk loc`
  note IH2 = `\<And>xs. \<lbrakk>call e2 = \<lfloor>(a, M', vs)\<rfloor>; n + max_vars e2 \<le> length xs; ?wt e2; None = None\<rbrakk> \<Longrightarrow> ?concl e2 n e2 xs 0 [] xs`
  note call = `call (e'\<bullet>F{D} := e2) = \<lfloor>(a, M', vs)\<rfloor>`
  note len = `n + max_vars (e'\<bullet>F{D} := e2) \<le> length xs`
  note xcp = `xcp = None`
  from `?wt (e\<bullet>F{D} := e2)` obtain E T1 T2 where wt1: "P,E \<turnstile>1 e :: T1" and wt2: "P,E \<turnstile>1 e2 :: T2" by auto
  note bisim1 = `P,e,n,h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, xcp)`
  show ?case
  proof(cases "is_val e'")
    case True
    then obtain v where [simp]: "e' = Val v" by auto
    from bisim1 wt1 have "\<tau>Exec_move P e h (stk, loc, pc, None) ([v], loc, length (compE2 e), None)"
      and [simp]: "xs = loc" by(auto dest!: bisim1Val2D1)
    hence "\<tau>Exec_move P (e\<bullet>F{D} := e2) h (stk, loc, pc, None) ([v], loc, length (compE2 e), None)"
      by-(rule FAss_\<tau>Exec_meth_xt1)
    also from call IH2[of loc] len wt2 obtain pc' stk' loc'
      where exec: "\<tau>Exec_move P e2 h ([], xs, 0, None) (rev vs @ Addr a # stk', loc', pc', None)"
      and ins: "compE2 e2 ! pc' = Invoke M' (length vs)" "pc' < length (compE2 e2)"
      and bisim': "P,e2,n,h \<turnstile> clearInitBlock e2 xs \<leftrightarrow> (rev vs @ Addr a # stk', loc', pc', None)" by auto
    from FAss_\<tau>Exec_meth_xt2[OF exec, of e F D v]
    have "\<tau>Exec_move P (e\<bullet>F{D} := e2) h ([v], loc, length (compE2 e), None) (rev vs @ Addr a # (stk' @ [v]), loc', length (compE2 e) + pc', None)" by simp
    also from bisim' `bsok e n`
    have "P,e\<bullet>F{D} := e2,n,h \<turnstile> (Val v\<bullet>F{D} := fst (clearInitBlock e2 xs), snd (clearInitBlock e2 xs)) \<leftrightarrow> ((rev vs @ Addr a # stk') @ [v], loc', length (compE2 e) + pc', None)"
      by - (rule bisim1FAss2, simp)
    ultimately show ?thesis using ins by fastsimp
  next
    case False with IH1 wt1 len `bsok e2 n` False xcp call show ?thesis
      by(clarsimp simp add: WT1_ex_simp)(fastsimp intro: bisim1_bisims1.bisim1FAss1 intro!: exI)
  qed
next
  case (bisim1FAss2 e2 n e' xs stk loc pc xcp e F D v)
  then obtain pc' loc' stk' where pc': "pc' < length (compE2 e2)" "compE2 e2 ! pc' = Invoke M' (length vs)"
    and exec: "\<tau>Exec_move P e2 h (stk, loc, pc, None) (rev vs @ Addr a # stk', loc', pc', None)"
    and bisim': "P,e2,n,h \<turnstile> clearInitBlock e' xs \<leftrightarrow> (rev vs @ Addr a # stk', loc', pc', None)" by fastsimp
  from exec have "\<tau>Exec_move P (e\<bullet>F{D} := e2) h (stk @ [v], loc, length (compE2 e) + pc, None)
                                       ((rev vs @ Addr a # stk') @ [v], loc', length (compE2 e) + pc', None)"
    by(rule FAss_\<tau>Exec_meth_xt2)
  moreover from bisim' `bsok e n`
  have "P,e\<bullet>F{D} := e2,n,h \<turnstile> (Val v\<bullet>F{D} := fst (clearInitBlock e' xs), snd (clearInitBlock e' xs)) \<leftrightarrow> ((rev vs @ Addr a # stk') @ [v], loc', length (compE2 e) + pc', None)"
    by -(rule bisim1_bisims1.bisim1FAss2, simp)
  ultimately show ?case using pc' by(fastsimp)
next
  case bisim1FAssNull thus ?case by simp
next
  case bisim1FAssThrow1 thus ?case by simp
next
  case bisim1FAssThrow2 thus ?case by simp
next
  case bisim1FAss3 thus ?case by simp
next
  case (bisim1Call1 obj n obj' xs stk loc pc xcp ps M)
  note IH1 = `\<lbrakk>call obj' = \<lfloor>(a, M', vs)\<rfloor>; n + max_vars obj' \<le> length xs; ?wt obj; xcp = None\<rbrakk> \<Longrightarrow> ?concl obj n obj' xs pc stk loc`
  note IH2 = `\<And>xs. \<lbrakk>calls ps = \<lfloor>(a, M', vs)\<rfloor>; n + max_varss ps \<le> length xs; ?wts ps; None = None\<rbrakk> \<Longrightarrow> ?concls ps n ps xs 0 [] xs`
  note len = `n + max_vars (obj'\<bullet>M(ps)) \<le> length xs`
  note bisim1 = `P,obj,n,h \<turnstile> (obj', xs) \<leftrightarrow> (stk, loc, pc, xcp)`
  note call = `call (obj'\<bullet>M(ps)) = \<lfloor>(a, M', vs)\<rfloor>`
  from `?wt (obj\<bullet>M(ps))` obtain E T Ts where wt1: "P,E \<turnstile>1 obj :: T" and wt2: "P,E \<turnstile>1 ps [::] Ts" by auto
  from call show ?case
  proof(cases rule: call_callE)
    case CallObj
    hence "\<not> is_val obj'" by auto
    with CallObj IH1 len `bsoks ps n` `xcp = None` wt1 show ?thesis
      by(clarsimp simp add: WT1_ex_simp)(fastsimp intro: bisim1_bisims1.bisim1Call1 intro!: exI)
  next
    case (CallParams v)
    with bisim1 wt1 have "\<tau>Exec_move P obj h (stk, loc, pc, None) ([v], loc, length (compE2 obj), None)"
      and [simp]: "xs = loc" by(auto dest!: bisim1Val2D1)
    hence "\<tau>Exec_move P (obj\<bullet>M(ps)) h (stk, loc, pc, None) ([v], loc, length (compE2 obj), None)"
      by-(rule Call_\<tau>Exec_meth_xtObj)
    also from IH2[of loc] CallParams len wt2 obtain pc' stk' loc'
      where exec: "\<tau>Exec_moves P ps h ([], loc, 0, None) (rev vs @ Addr a # stk', loc', pc', None)"
      and ins: "compEs2 ps ! pc' = Invoke M' (length vs)" "pc' < length (compEs2 ps)"
      and bisim': "P,ps,n,h \<turnstile> clearInitBlocks ps xs [\<leftrightarrow>] (rev vs @ Addr a # stk',loc',pc',None)" by auto
    from Call_\<tau>Exec_meth_xtParams[OF exec, of obj M v]
    have "\<tau>Exec_move P (obj\<bullet>M(ps)) h ([v], loc, length (compE2 obj), None) (rev vs @ Addr a # (stk' @ [v]), loc', length (compE2 obj) + pc', None)" by simp
    also have "P,obj\<bullet>M(ps),n,h \<turnstile> (Val v\<bullet>M(fst (clearInitBlocks ps xs)), snd (clearInitBlocks ps xs)) \<leftrightarrow> ((rev vs @ Addr a # stk') @ [v], loc', length (compE2 obj) + pc', None)"
      using bisim' `bsok obj n` by -(rule bisim1CallParams, simp)
    ultimately show ?thesis using ins CallParams by fastsimp
  next
    case Call[simp]
    from bisim1 wt1 have "\<tau>Exec_move P obj h (stk, loc, pc, None) ([Addr a], loc, length (compE2 obj), None)"
      and [simp]: "xs = loc" by(auto dest!: bisim1Val2D1)
    hence "\<tau>Exec_move P (obj\<bullet>M(ps)) h (stk, loc, pc, None) ([Addr a], loc, length (compE2 obj), None)"
      by-(rule Call_\<tau>Exec_meth_xtObj)
    also have "\<tau>Exec_moves P ps h ([], xs, 0, None) (rev vs, xs, length (compEs2 ps), None)"
    proof(cases vs)
      case Nil with Call show ?thesis by(auto intro: \<tau>Execs_refl)
    next
      case Cons with wt2 Call bisims1_Val_\<tau>Exec_moves[OF bisims1_refl[of "map Val vs" n P h loc]]
      show ?thesis by(auto simp add: bsoks_def)
    qed
    from Call_\<tau>Exec_meth_xtParams[OF this, of obj M "Addr a"]
    have "\<tau>Exec_move P (obj\<bullet>M(ps)) h ([Addr a], loc, length (compE2 obj), None) (rev vs @ [Addr a], xs, length (compE2 obj) + length (compEs2 ps), None)" by simp
    also have "P,ps,n,h \<turnstile> (map Val vs,xs) [\<leftrightarrow>] (rev vs,xs,length (compEs2 ps),None)"
      by(rule bisims1_map_Val_append[OF bisims1Nil, simplified])(simp_all add: bsoks_def)
    hence "P,obj\<bullet>M(ps),n,h \<turnstile> (addr a\<bullet>M(map Val vs), xs) \<leftrightarrow> (rev vs @ [Addr a], xs, length (compE2 obj) + length (compEs2 ps), None)"
      using `bsok obj n` by(rule bisim1CallParams)
    ultimately show ?thesis by fastsimp
  qed
next
  case (bisim1CallParams ps n ps' xs stk loc pc xcp obj M v)
  note IH2 = `\<lbrakk>calls ps' = \<lfloor>(a, M', vs)\<rfloor>; n + max_varss ps' \<le> length xs; ?wts ps; xcp = None\<rbrakk> \<Longrightarrow> ?concls ps n ps' xs pc stk loc`
  note bisim2 = `P,ps,n,h \<turnstile> (ps', xs) [\<leftrightarrow>] (stk, loc, pc, xcp)`
  note call = `call (Val v\<bullet>M(ps')) = \<lfloor>(a, M', vs)\<rfloor>`
  note len = `n + max_vars (Val v\<bullet>M(ps')) \<le> length xs`
  from `?wt (obj\<bullet>M(ps))` obtain T Ts E where wt1: "P,E \<turnstile>1 obj :: T" and wt2: "P,E \<turnstile>1 ps [::] Ts" by auto
  from call show ?case
  proof(cases rule: call_callE)
    case CallObj thus ?thesis by simp
  next
    case (CallParams v')
    with IH2 len `xcp = None` wt2 obtain pc' stk' loc'
      where exec: "\<tau>Exec_moves P ps h (stk, loc, pc, None) (rev vs @ Addr a # stk', loc', pc', None)"
      and ins: "pc' < length (compEs2 ps)" "compEs2 ps ! pc' = Invoke M' (length vs)"
      and bisim': "P,ps,n,h \<turnstile> clearInitBlocks ps' xs [\<leftrightarrow>] (rev vs @ Addr a # stk',loc',pc',None)" by auto
    from exec have "\<tau>Exec_move P (obj\<bullet>M(ps)) h (stk @ [v], loc, length (compE2 obj) + pc, None)
                                ((rev vs @ Addr a # stk') @ [v], loc', length (compE2 obj) + pc', None)"
      by(rule Call_\<tau>Exec_meth_xtParams)
    moreover have "P,obj\<bullet>M(ps),n,h \<turnstile> (Val v\<bullet>M(fst (clearInitBlocks ps' xs)), snd (clearInitBlocks ps' xs)) \<leftrightarrow>
                                     ((rev vs @ Addr a # stk') @ [v], loc', length (compE2 obj) + pc', None)"
      using bisim' `bsok obj n` by-(rule bisim1_bisims1.bisim1CallParams, simp)
    ultimately show ?thesis using ins by fastsimp
  next
    case Call
    hence [simp]: "v = Addr a" "ps' = map Val vs" "M' = M" by simp_all
    have "xs = loc \<and> \<tau>Exec_moves P ps h (stk, loc, pc, None) (rev vs, loc, length (compEs2 ps), None)"
    proof(cases "pc < length (compEs2 ps)")
      case True with bisim2 wt2 show ?thesis by(auto dest: bisims1_Val_\<tau>Exec_moves)
    next
      case False
      from bisim2 have "pc \<le> length (compEs2 ps)" by(rule bisims1_pc_length_compEs2)
      with False have "pc = length (compEs2 ps)" by simp
      with bisim2 show ?thesis by(auto dest: bisims1_Val_length_compEs2D intro: \<tau>Execs_refl)
    qed
    then obtain [simp]: "xs = loc"
      and exec: "\<tau>Exec_moves P ps h (stk, loc, pc, None) (rev vs, loc, length (compEs2 ps), None)" ..
    from exec have "\<tau>Exec_move P (obj\<bullet>M(ps)) h (stk @ [v], loc, length (compE2 obj) + pc, None)
                              (rev vs @ [v], loc, length (compE2 obj) + length (compEs2 ps), None)"
      by(rule Call_\<tau>Exec_meth_xtParams)
    moreover from bisim2 have len: "length ps = length ps'" by(auto dest: bisims1_lengthD)
    moreover have "P,ps,n,h \<turnstile> (map Val vs,xs) [\<leftrightarrow>] (rev vs,xs,length (compEs2 ps),None)" using len `bsoks ps n`
      by-(rule bisims1_map_Val_append[OF bisims1Nil, simplified], simp_all)
    hence "P,obj\<bullet>M(ps),n,h \<turnstile> (addr a\<bullet>M(map Val vs), xs) \<leftrightarrow> (rev vs @ [Addr a], xs, length (compE2 obj) + length (compEs2 ps), None)" using `bsok obj n` by -(erule bisim1_bisims1.bisim1CallParams, simp)
    ultimately show ?thesis by fastsimp
  qed
next
  case bisim1CallThrow thus ?case by simp
next
  case bisim1CallThrowObj thus ?case by simp
next
  case bisim1CallThrowParams thus ?case by simp
next
  case (bisim1BlockSome1 e V T v xs)
  note IH = `\<And>xs. \<lbrakk>call e = \<lfloor>(a, M', vs)\<rfloor>; Suc V + max_vars e \<le> length xs; ?wt e; None = None\<rbrakk> \<Longrightarrow> ?concl e (Suc V) e xs 0 [] xs`
  note call = `call {V:T=\<lfloor>v\<rfloor>; e}\<^bsub>False\<^esub> = \<lfloor>(a, M', vs)\<rfloor>`
  note len = `V + max_vars {V:T=\<lfloor>v\<rfloor>; e}\<^bsub>False\<^esub> \<le> length xs`
  from `?wt {V:T=\<lfloor>v\<rfloor>; e}\<^bsub>False\<^esub>` obtain E Te where wte: "P,E@[T] \<turnstile>1 e :: Te" and v: "\<not> is_Addr v" by auto
  from len v have "\<tau>Exec_move P {V:T=\<lfloor>v\<rfloor>; e}\<^bsub>False\<^esub> h ([], xs, 0, None) ([], xs[V := v], Suc (Suc 0), None)"
    by -(rule \<tau>Exec2step,auto intro!: exec_instr intro: \<tau>move2_\<tau>moves2.intros simp add: exec_move_def)
  also from IH[of "xs[V := v]"] call len wte obtain pc' loc' stk'
    where exec: "\<tau>Exec_move P e h ([], xs[V := v], 0, None) (rev vs @ Addr a # stk', loc', pc', None)"
    and pc': "pc' < length (compE2 e)" "compE2 e ! pc' = Invoke M' (length vs)"
    and bisim': "P,e,Suc V,h \<turnstile> clearInitBlock e (xs[V := v]) \<leftrightarrow> (rev vs @ Addr a # stk', loc', pc', None)" by auto
  note Block_\<tau>Exec_meth_xtSome[OF exec, of V T v] also from bisim'
  have "P,{V:T=\<lfloor>v\<rfloor>; e}\<^bsub>False\<^esub>,V,h \<turnstile> ({V:T=None; fst (clearInitBlock e (xs[V := v]))}\<^bsub>False\<^esub>, snd (clearInitBlock e (xs[V := v]))) \<leftrightarrow> (rev vs @ Addr a # stk', loc', Suc (Suc pc'), None)"
    by-(rule bisim1BlockSome4, simp)
  ultimately show ?case using pc' by fastsimp
next
  case (bisim1BlockSome2 e V T v xs)
  note IH = `\<And>xs. \<lbrakk>call e = \<lfloor>(a, M', vs)\<rfloor>; Suc V + max_vars e \<le> length xs; ?wt e; None = None\<rbrakk> \<Longrightarrow> ?concl e (Suc V) e xs 0 [] xs`
  note call = `call {V:T=\<lfloor>v\<rfloor>; e}\<^bsub>False\<^esub> = \<lfloor>(a, M', vs)\<rfloor>`
  note len = `V + max_vars {V:T=\<lfloor>v\<rfloor>; e}\<^bsub>False\<^esub> \<le> length xs`
  from `?wt {V:T=\<lfloor>v\<rfloor>; e}\<^bsub>False\<^esub>` obtain E Te where wte: "P,E@[T] \<turnstile>1 e :: Te" by auto
  from len have "\<tau>Exec_move P {V:T=\<lfloor>v\<rfloor>; e}\<^bsub>False\<^esub> h ([v], xs, Suc 0, None) ([], xs[V := v], Suc (Suc 0), None)"
    by -(rule \<tau>Exec1step,auto intro: exec_instr \<tau>move2_\<tau>moves2.intros simp add: exec_move_def)
  also from IH[of "xs[V := v]"] call len wte obtain pc' loc' stk'
    where exec: "\<tau>Exec_move P e h ([], xs[V := v], 0, None) (rev vs @ Addr a # stk', loc', pc', None)"
    and pc': "pc' < length (compE2 e)" "compE2 e ! pc' = Invoke M' (length vs)"
    and bisim': "P,e,Suc V,h \<turnstile> clearInitBlock e (xs[V := v]) \<leftrightarrow> (rev vs @ Addr a # stk', loc', pc', None)" by auto
  note Block_\<tau>Exec_meth_xtSome[OF exec, of V T v] also from bisim'
  have "P,{V:T=\<lfloor>v\<rfloor>; e}\<^bsub>False\<^esub>,V,h \<turnstile> ({V:T=None; fst (clearInitBlock e (xs[V := v]))}\<^bsub>False\<^esub>, snd (clearInitBlock e (xs[V := v]))) \<leftrightarrow> (rev vs @ Addr a # stk', loc', Suc (Suc pc'), None)"
    by-(rule bisim1BlockSome4, simp)
  ultimately show ?case using pc' by fastsimp
next
  case (bisim1BlockSome3 e V e' xs v stk loc pc xcp T)
  then obtain pc' loc' stk' where pc': "pc' < length (compE2 e)" "compE2 e ! pc' = Invoke M' (length vs)"
    and exec: "\<tau>Exec_move P e h (stk, loc, pc, None) (rev vs @ Addr a # stk', loc', pc', None)"
    and bisim': "P,e,Suc V,h \<turnstile> clearInitBlock e' (xs[V := v]) \<leftrightarrow> (rev vs @ Addr a # stk', loc', pc', None)" by auto
  note Block_\<tau>Exec_meth_xtSome[OF exec, of V T v]
  moreover from bisim' have "P,{V:T=\<lfloor>v\<rfloor>; e}\<^bsub>False\<^esub>,V,h \<turnstile> ({V:T=None; fst (clearInitBlock e' (xs[V := v]))}\<^bsub>False\<^esub>, snd (clearInitBlock e' (xs[V := v]))) \<leftrightarrow> (rev vs @ Addr a # stk', loc', Suc (Suc pc'), None)"
    by-(rule bisim1BlockSome4, simp)
  ultimately show ?case using pc' by fastsimp
next
  case (bisim1BlockSome4 e V e' xs stk loc pc xcp T v)
  then obtain pc' loc' stk' where pc': "pc' < length (compE2 e)" "compE2 e ! pc' = Invoke M' (length vs)"
    and exec: "\<tau>Exec_move P e h (stk, loc, pc, None) (rev vs @ Addr a # stk', loc', pc', None)"
    and bisim': "P,e,Suc V,h \<turnstile> clearInitBlock e' xs \<leftrightarrow> (rev vs @ Addr a # stk', loc', pc', None)" by auto
  note Block_\<tau>Exec_meth_xtSome[OF exec, of V T v]
  moreover from bisim' have "P,{V:T=\<lfloor>v\<rfloor>; e}\<^bsub>False\<^esub>,V,h \<turnstile> ({V:T=None; fst (clearInitBlock e' xs)}\<^bsub>False\<^esub>, snd (clearInitBlock e' xs)) \<leftrightarrow> (rev vs @ Addr a # stk', loc', Suc (Suc pc'), None)"
    by-(rule bisim1_bisims1.bisim1BlockSome4, simp)
  ultimately show ?case using pc' by fastsimp
next  
  case bisim1BlockThrowSome thus ?case by simp
next
  case (bisim1BlockNone e V e' xs stk loc pc xcp T)
  then obtain pc' loc' stk' where pc': "pc' < length (compE2 e)" "compE2 e ! pc' = Invoke M' (length vs)"
    and exec: "\<tau>Exec_move P e h (stk, loc, pc, None) (rev vs @ Addr a # stk', loc', pc', None)"
    and bisim': "P,e,Suc V,h \<turnstile> clearInitBlock e' xs \<leftrightarrow> (rev vs @ Addr a # stk', loc', pc', None)" by auto
  note Block_\<tau>Exec_meth_xtNone[OF exec, of V T]
  moreover from bisim' have "P,{V:T=None; e}\<^bsub>False\<^esub>,V,h \<turnstile> ({V:T=None; fst (clearInitBlock e' xs)}\<^bsub>False\<^esub>, snd (clearInitBlock e' xs)) \<leftrightarrow> (rev vs @ Addr a # stk', loc', pc', None)"
    by-(rule bisim1_bisims1.bisim1BlockNone, simp)
  ultimately show ?case using pc' by fastsimp
next
  case bisim1BlockThrowNone thus ?case by simp
next
  case bisim1Sync1 thus ?case
    by (auto simp add: WT1_ex_simp)(fastsimp intro: bisim1_bisims1.bisim1Sync1 intro!: exI)
next
  case bisim1Sync2 thus ?case by simp
next
  case bisim1Sync3 thus ?case by simp
next
  case bisim1Sync4 thus ?case
    by (auto simp add: WT1_ex_simp)(fastsimp intro: bisim1_bisims1.bisim1Sync4 intro!: exI)
next
  case bisim1Sync5 thus ?case by simp
next
  case bisim1Sync6 thus ?case by simp
next
  case bisim1Sync7 thus ?case by simp
next
  case bisim1Sync8 thus ?case by simp
next
  case bisim1Sync9 thus ?case by simp
next
  case bisim1Sync10 thus ?case by simp
next
  case bisim1Sync11 thus ?case by simp
next
  case bisim1Sync12 thus ?case by simp
next
  case bisim1Sync13 thus ?case by simp
next
  case bisim1Sync14 thus ?case by simp
next
  case bisim1Sync15 thus ?case by simp
next
  case bisim1SyncThrow thus ?case by simp
next
  case bisim1Seq1 thus ?case
    by (auto simp add: WT1_ex_simp)(fastsimp intro: bisim1_bisims1.bisim1Seq1 intro!: exI)
next
  case bisim1SeqThrow1 thus ?case by simp
next
  case (bisim1Seq2 e2 n e' xs stk loc pc xcp e1)
  then obtain pc' loc' stk' where pc': "pc' < length (compE2 e2)" "compE2 e2 ! pc' = Invoke M' (length vs)"
    and exec: "\<tau>Exec_move P e2 h (stk, loc, pc, None) (rev vs @ Addr a # stk', loc', pc', None)"
    and bisim': "P,e2,n,h \<turnstile> clearInitBlock e' xs \<leftrightarrow> (rev vs @ Addr a # stk', loc', pc', None)" by auto
  from Seq_\<tau>Exec_meth_xt2[OF exec, of e1] pc' bisim' `bsok e1 n`
  show ?case by(fastsimp intro: bisim1_bisims1.bisim1Seq2 intro!: exI)
next
  case bisim1Cond1 thus ?case
    by (auto simp add: WT1_ex_simp) (fastsimp intro: bisim1_bisims1.bisim1Cond1 intro!: exI)+
next
  case (bisim1CondThen e1 n e' xs stk loc pc xcp e e2)
  then obtain pc' loc' stk' where pc': "pc' < length (compE2 e1)" "compE2 e1 ! pc' = Invoke M' (length vs)"
    and exec: "\<tau>Exec_move P e1 h (stk, loc, pc, None) (rev vs @ Addr a # stk', loc', pc', None)"
    and bisim': "P,e1,n,h \<turnstile> clearInitBlock e' xs \<leftrightarrow> (rev vs @ Addr a # stk', loc', pc', None)" by auto
  from Cond_\<tau>Exec_meth_xt_then[OF exec] pc' bisim' `bsok e n` `bsok e2 n` show ?case
    by(fastsimp intro: bisim1_bisims1.bisim1CondThen intro!: exI)
next
  case (bisim1CondElse e2 n e' xs stk loc pc xcp e e1)
  then obtain pc' loc' stk' where pc': "pc' < length (compE2 e2)" "compE2 e2 ! pc' = Invoke M' (length vs)"
    and exec: "\<tau>Exec_move P e2 h (stk, loc, pc, None) (rev vs @ Addr a # stk', loc', pc', None)"
    and bisim': "P,e2,n,h \<turnstile> clearInitBlock e' xs \<leftrightarrow> (rev vs @ Addr a # stk', loc', pc', None)" by auto
  from Cond_\<tau>Exec_meth_xt_else[OF exec] pc' bisim' `bsok e n` `bsok e1 n` show ?case
    by (fastsimp intro: bisim1_bisims1.bisim1CondElse intro!: exI)
next
  case bisim1CondThrow thus ?case by simp
next
  case bisim1While1 thus ?case by simp
next
  case bisim1While3 thus ?case
    by (auto simp add: WT1_ex_simp)(fastsimp intro: bisim1_bisims1.bisim1While3 intro!: exI)+
next
  case bisim1While4 thus ?case
    by (auto simp add: WT1_ex_simp)(fastsimp intro!: While_\<tau>Exec_meth_xt2 bisim1_bisims1.bisim1While4 exI)+
next
  case bisim1While6 thus ?case by simp
next
  case bisim1While7 thus ?case by simp
next
  case bisim1WhileThrow1 thus ?case by simp
next
  case bisim1WhileThrow2 thus ?case by simp
next
  case bisim1Throw1 thus ?case
    by (auto simp add: WT1_ex_simp)(fastsimp intro!: exI bisim1_bisims1.bisim1Throw1)+
next
  case bisim1Throw2 thus ?case by simp
next
  case bisim1ThrowNull thus ?case by simp
next
  case bisim1ThrowThrow thus ?case by simp
next
  case bisim1Try thus ?case
    by (auto simp add: WT1_ex_simp)(fastsimp intro: bisim1_bisims1.bisim1Try intro!: exI)+
next
  case (bisim1TryCatch1 e V a' xs stk loc pc C' fs C e2)
  note IH2 = `\<And>xs. \<lbrakk>call e2 = \<lfloor>(a, M', vs)\<rfloor>; Suc V + max_vars e2 \<le> length xs; ?wt e2; None = None\<rbrakk> \<Longrightarrow> ?concl e2 (Suc V) e2 xs 0 [] xs`
  note bisim1 = `P,e,V,h \<turnstile> (Throw a', xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a'\<rfloor>)`
  note bisim2 = `\<And>xs. P,e2,Suc V,h \<turnstile> (e2, xs) \<leftrightarrow> ([], xs, 0, None)`
  note len = `V + max_vars {V:Class C=None; e2}\<^bsub>False\<^esub> \<le> length (xs[V := Addr a'])`
  from `?wt (try e catch(C V) e2)` obtain E T T2 where wt1: "P,E \<turnstile>1 e :: T" and wt2: "P,E@[Class C] \<turnstile>1 e2 :: T2" by auto
  from bisim1 have [simp]: "xs = loc" by(auto dest: bisim1_ThrowD)
  from len have "\<tau>Exec_move P (try e catch(C V) e2) h ([Addr a'], loc, Suc (length (compE2 e)), None) ([], loc[V := Addr a'], Suc (Suc (length (compE2 e))), None)"
    by -(rule \<tau>Exec1step,auto simp add: exec_move_def intro: \<tau>move2_\<tau>moves2.intros exec_instr)
  also from IH2[of "loc[V := Addr a']"] `bsok e2 (Suc V)` len `call {V:Class C=None; e2}\<^bsub>False\<^esub> = \<lfloor>(a, M', vs)\<rfloor>` wt2
  obtain pc' loc' stk'
    where exec: "\<tau>Exec_move P e2 h ([], loc[V := Addr a'], 0, None) (rev vs @ Addr a # stk', loc', pc', None)"
    and ins: "pc' < length (compE2 e2)" "compE2 e2 ! pc' = Invoke M' (length vs)"
    and bisim': "P,e2,Suc V,h \<turnstile> clearInitBlock e2 (loc[V := Addr a']) \<leftrightarrow> (rev vs @ Addr a # stk', loc', pc', None)" by auto
  from Try_\<tau>Exec_meth_xt2[OF exec, of e C V]
  have "\<tau>Exec_move P (try e catch(C V) e2) h ([], loc[V := Addr a'], Suc (Suc (length (compE2 e))), None) (rev vs @ Addr a # stk', loc', Suc (Suc (length (compE2 e) + pc')), None)" by simp
  also from bisim' `bsok e V`
  have "P,try e catch(C V) e2,V,h \<turnstile> ({V:Class C=None; fst (clearInitBlock e2 (loc[V := Addr a']))}\<^bsub>False\<^esub>, snd (clearInitBlock e2 (loc[V := Addr a']))) \<leftrightarrow> (rev vs @ Addr a # stk', loc', (Suc (Suc (length (compE2 e) + pc'))), None)"
    by -(rule bisim1TryCatch2, simp)
  ultimately show ?case using ins by fastsimp
next
  case bisim1TryCatch2 thus ?case
    by (auto simp add: WT1_ex_simp)(fastsimp intro!: Try_\<tau>Exec_meth_xt2 bisim1_bisims1.bisim1TryCatch2 exI)+
next
  case bisim1TryFail thus ?case by simp
next
  case bisim1TryCatchThrow thus ?case by simp
next
  case bisims1Nil thus ?case by simp
next
  case (bisims1List1 e n e' xs stk loc pc xcp es)
  note IH1 = `\<lbrakk>call e' = \<lfloor>(a, M', vs)\<rfloor>; n + max_vars e' \<le> length xs; ?wt e; xcp = None\<rbrakk> \<Longrightarrow> ?concl e n e' xs pc stk loc`
  note IH2 = `\<And>xs. \<lbrakk>calls es = \<lfloor>(a, M', vs)\<rfloor>; n + max_varss es \<le> length xs; ?wts es; None = None\<rbrakk> \<Longrightarrow> ?concls es n es xs 0 [] xs`
  note bisim1 = `P,e,n,h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, xcp)`
  note call = `calls (e' # es) = \<lfloor>(a, M', vs)\<rfloor>`
  note len = `n + max_varss (e' # es) \<le> length xs`
  from `?wts (e # es)` obtain E T Ts where wte: "P,E \<turnstile>1 e :: T" and wtes: "P,E \<turnstile>1 es [::] Ts" by auto
  show ?case
  proof(cases "is_val e'")
    case True
    then obtain v where [simp]: "e' = Val v" by auto
    with bisim1 wte have "\<tau>Exec_move P e h (stk, loc, pc, None) ([v], loc, length (compE2 e), None)"
      and [simp]: "xs = loc" by(auto dest!: bisim1Val2D1)
    hence "\<tau>Exec_moves P (e # es) h (stk, loc, pc, None) ([v], loc, length (compE2 e), None)"
      by-(rule \<tau>Exec_move_\<tau>Exec_moves)
    also from call IH2[of loc] len wtes obtain pc' stk' loc'
      where exec: "\<tau>Exec_moves P es h ([], xs, 0, None) (rev vs @ Addr a # stk', loc', pc', None)"
      and ins: "compEs2 es ! pc' = Invoke M' (length vs)" "pc' < length (compEs2 es)"
      and bisim': "P,es,n,h \<turnstile> clearInitBlocks es xs [\<leftrightarrow>] (rev vs @ Addr a # stk',loc',pc',None)" by auto
    from append_\<tau>Exec_moves[OF _ exec, of "[v]" "[e]"]
    have "\<tau>Exec_moves P (e # es) h ([v], loc, length (compE2 e), None) (rev vs @ Addr a # (stk' @ [v]), loc', length (compE2 e) + pc', None)"
      by simp
    also from bisim' `bsok e n`
    have "P,e # es,n,h \<turnstile> (Val v # fst (clearInitBlocks es xs),snd (clearInitBlocks es xs)) [\<leftrightarrow>]
                         ((rev vs @ Addr a # stk') @ [v],loc',length (compE2 e) + pc',None)"
      by-(rule bisim1_bisims1.bisims1List2, simp)
    ultimately show ?thesis using ins by fastsimp
  next
    case False
    with call IH1 wte len `xcp = None` `bsoks es n` show ?thesis
      by (auto simp add: WT1_ex_simp)(fastsimp intro!: \<tau>Exec_move_\<tau>Exec_moves bisim1_bisims1.bisims1List1 exI)+
  qed
next
  case (bisims1List2 es n es' xs stk loc pc xcp e v)
  then obtain pc' stk' loc' where pc': "pc' < length (compEs2 es)" "compEs2 es ! pc' = Invoke M' (length vs)"
    and exec: "\<tau>Exec_moves P es h (stk, loc, pc, None) (rev vs @ Addr a # stk', loc', pc', None)"
    and bisim': "P,es,n,h \<turnstile> clearInitBlocks es' xs [\<leftrightarrow>] (rev vs @ Addr a # stk', loc', pc', None)" by auto
  note append_\<tau>Exec_moves[OF _ exec, of "[v]" "[e]"]
  moreover from bisim' `bsok e n`
  have "P,e#es,n,h \<turnstile> (Val v#fst (clearInitBlocks es' xs),snd (clearInitBlocks es' xs)) [\<leftrightarrow>] ((rev vs @ Addr a # stk') @ [v],loc',length (compE2 e) + pc',None)"
    by-(rule bisim1_bisims1.bisims1List2, simp)
  ultimately show ?case using pc' by fastsimp
qed


lemma fixes P :: J1_prog
  shows bisim1_inline_call_Val:
  "\<lbrakk> P,e,n,h \<turnstile> (e', xs) \<leftrightarrow> (rev vs @ Addr a # stk, loc, pc, None); call e' = \<lfloor>(a, M, vs)\<rfloor>;
     compE2 e ! pc = Invoke M (length vs) \<rbrakk>
    \<Longrightarrow> P,e,n,h \<turnstile> (inline_call (Val v) (fst (clearInitBlock e' xs)), snd (clearInitBlock e' xs)) \<leftrightarrow> (v # stk, loc, Suc pc, None)"
  (is "\<lbrakk> _; _; _ \<rbrakk> \<Longrightarrow> ?concl e n e' xs pc stk loc")

  and bisims1_inline_calls_Val:
  "\<lbrakk> P,es,n,h \<turnstile> (es',xs) [\<leftrightarrow>] (rev vs @ Addr a # stk,loc,pc,None); calls es' = \<lfloor>(a, M, vs)\<rfloor>;
     compEs2 es ! pc = Invoke M (length vs) \<rbrakk>
    \<Longrightarrow> P,es,n,h \<turnstile> (inline_calls (Val v) (fst (clearInitBlocks es' xs)),snd (clearInitBlocks es' xs)) [\<leftrightarrow>] (v # stk,loc,Suc pc,None)"
  (is "\<lbrakk> _; _; _ \<rbrakk> \<Longrightarrow> ?concls es n es' xs pc stk loc")
proof(induct e n e' xs STK\<equiv>"rev vs @ Addr a # stk" loc pc xcp\<equiv>"None :: addr option"
        and es n es' xs STK\<equiv>"rev vs @ Addr a # stk" loc pc xcp\<equiv>"None :: addr option"
     arbitrary: stk and stk rule: bisim1_bisims1_inducts_split)
  case bisim1Val2 thus ?case by simp
next
  case bisim1New thus ?case by simp
next
  case bisim1NewThrow thus ?case by simp
next
  case bisim1NewArray thus ?case
    by(auto split: split_if_asm dest: bisim1_pc_length_compE2 intro: bisim1_bisims1.bisim1NewArray)
next
  case bisim1NewArrayNegative thus ?case by simp
next
  case bisim1NewArrayFail thus ?case by simp
next
  case bisim1NewArrayThrow thus ?case by simp
next
  case bisim1Cast thus ?case
    by(auto split: split_if_asm dest: bisim1_pc_length_compE2 intro: bisim1_bisims1.bisim1Cast)
next
  case bisim1CastFail thus ?case by simp
next
  case bisim1CastThrow thus ?case by simp
next
  case bisim1Val thus ?case by simp
next
  case bisim1Var thus ?case by simp
next
  case (bisim1BinOp1 e1 n e' xs STK loc pc xcp e2 bop)
  note IH1 = `\<lbrakk>call e' = \<lfloor>(a, M, vs)\<rfloor>; compE2 e1 ! pc = Invoke M (length vs);
               STK = rev vs @ Addr a # stk; xcp = None\<rbrakk> \<Longrightarrow> ?concl e1 n e' xs pc stk loc`
  note bisim1 = `P,e1,n,h \<turnstile> (e', xs) \<leftrightarrow> (STK, loc, pc, xcp)`
  note call = `call (e' \<guillemotleft>bop\<guillemotright> e2) = \<lfloor>(a, M, vs)\<rfloor>`
  note ins = `compE2 (e1 \<guillemotleft>bop\<guillemotright> e2) ! pc = Invoke M (length vs)`
  show ?case
  proof(cases "is_val e'")
    case False
    with bisim1 call have "pc < length (compE2 e1)" by(auto intro: bisim1_call_pcD)
    with call ins False IH1 `bsok e2 n` `STK = rev vs @ Addr a # stk` `xcp = None` show ?thesis
      by(auto intro: bisim1_bisims1.bisim1BinOp1)
  next
    case True
    then obtain v where [simp]: "e' = Val v" by auto
    from bisim1 have "pc \<le> length (compE2 e1)" by(auto dest: bisim1_pc_length_compE2)
    moreover {
      assume pc: "pc < length (compE2 e1)"
      with bisim1 ins have False by(auto dest: bisim_Val_pc_not_Invoke simp add: nth_append) }
    ultimately have [simp]: "pc = length (compE2 e1)" by(cases "pc < length (compE2 e1)") auto
    with ins have False by(simp)
    thus ?thesis ..
  qed
next
  case (bisim1BinOp2 e2 n e' xs STK loc pc xcp e1 bop v1)
  note IH2 = `\<And>stk. \<lbrakk>call e' = \<lfloor>(a, M, vs)\<rfloor>; compE2 e2 ! pc = Invoke M (length vs);
                     STK = rev vs @ Addr a # stk; xcp = None\<rbrakk> \<Longrightarrow> ?concl e2 n e' xs pc stk loc`
  note bisim2 = `P,e2,n,h \<turnstile> (e', xs) \<leftrightarrow> (STK, loc, pc, xcp)`
  note call = `call (Val v1 \<guillemotleft>bop\<guillemotright> e') = \<lfloor>(a, M, vs)\<rfloor>`
  note ins = `compE2 (e1 \<guillemotleft>bop\<guillemotright> e2) ! (length (compE2 e1) + pc) = Invoke M (length vs)`
  note stk = `STK @ [v1] = rev vs @ Addr a # stk`
  from call bisim2 have pc: "pc < length (compE2 e2)" by(auto intro: bisim1_call_pcD)
  with ins have ins': "compE2 e2 ! pc = Invoke M (length vs)" by(simp)
  from bisim1_Invoke_stkD[OF bisim2[unfolded `xcp = None`] pc this]
  obtain vs' v stk' where [simp]: "STK = vs' @ v # stk'" and "length vs' = length vs" by auto
  with stk have [simp]: "vs' = rev vs" "v = Addr a" "stk = stk' @ [v1]" by auto
  from IH2[of stk'] ins' pc `bsok e1 n` `xcp = None` call show ?case
    by(auto dest: bisim1_bisims1.bisim1BinOp2)
next
  case bisim1BinOpThrow1 thus ?case by simp
next
  case bisim1BinOpThrow2 thus ?case by simp
next
  case bisim1LAss1 thus ?case
    by(auto split: split_if_asm dest: bisim1_pc_length_compE2 intro: bisim1_bisims1.bisim1LAss1)
next
  case bisim1LAss2 thus ?case by simp
next
  case bisim1LAssThrow thus ?case by simp
next
  case (bisim1AAcc1 A n a' xs STK loc pc xcp i)
  note IH1 = `\<lbrakk>call a' = \<lfloor>(a, M, vs)\<rfloor>; compE2 A ! pc = Invoke M (length vs);
               STK = rev vs @ Addr a # stk; xcp = None\<rbrakk> \<Longrightarrow> ?concl A n a' xs pc stk loc`
  note bisim1 = `P,A,n,h \<turnstile> (a', xs) \<leftrightarrow> (STK, loc, pc, xcp)`
  note call = `call (a'\<lfloor>i\<rceil>) = \<lfloor>(a, M, vs)\<rfloor>`
  note ins = `compE2 (A\<lfloor>i\<rceil>) ! pc = Invoke M (length vs)`
  show ?case
  proof(cases "is_val a'")
    case False
    with bisim1 call have "pc < length (compE2 A)" by(auto intro: bisim1_call_pcD)
    with call ins False IH1 `bsok i n` `STK = rev vs @ Addr a # stk` `xcp = None` show ?thesis
      by(auto intro: bisim1_bisims1.bisim1AAcc1)
  next
    case True
    then obtain v where [simp]: "a' = Val v" by auto
    from bisim1 have "pc \<le> length (compE2 A)" by(auto dest: bisim1_pc_length_compE2)
    moreover {
      assume pc: "pc < length (compE2 A)"
      with bisim1 ins have False by(auto dest: bisim_Val_pc_not_Invoke simp add: nth_append) }
    ultimately have [simp]: "pc = length (compE2 A)" by(cases "pc < length (compE2 A)") auto
    with ins have False by(simp)
    thus ?thesis ..
  qed
next
  case (bisim1AAcc2 i n i' xs STK loc pc xcp A v)
  note IH2 = `\<And>stk. \<lbrakk>call i' = \<lfloor>(a, M, vs)\<rfloor>; compE2 i ! pc = Invoke M (length vs);
                     STK = rev vs @ Addr a # stk; xcp = None\<rbrakk> \<Longrightarrow> ?concl i n i' xs pc stk loc`
  note bisim2 = `P,i,n,h \<turnstile> (i', xs) \<leftrightarrow> (STK, loc, pc, xcp)`
  note call = `call (Val v\<lfloor>i'\<rceil>) = \<lfloor>(a, M, vs)\<rfloor>`
  note ins = `compE2 (A\<lfloor>i\<rceil>) ! (length (compE2 A) + pc) = Invoke M (length vs)`
  note stk = `STK @ [v] = rev vs @ Addr a # stk`
  from call bisim2 have pc: "pc < length (compE2 i)" by(auto intro: bisim1_call_pcD)
  with ins have ins': "compE2 i ! pc = Invoke M (length vs)" by(simp)
  from bisim1_Invoke_stkD[OF bisim2[unfolded `xcp = None`] pc this]
  obtain vs' v' stk' where [simp]: "STK = vs' @ v' # stk'" and "length vs' = length vs" by auto
  with stk have [simp]: "vs' = rev vs" "v' = Addr a" "stk = stk' @ [v]" by auto
  from IH2[of stk'] ins' pc `bsok A n` `xcp = None` call show ?case
    by(auto dest: bisim1_bisims1.bisim1AAcc2)
next
  case bisim1AAccThrow1 thus ?case by simp
next
  case bisim1AAccThrow2 thus ?case by simp
next
  case bisim1AAccBounds thus ?case by simp
next
  case bisim1AAccNull thus ?case by simp
next
  case (bisim1AAss1 A n a' xs STK loc pc xcp i e)
  note IH1 = `\<lbrakk>call a' = \<lfloor>(a, M, vs)\<rfloor>; compE2 A ! pc = Invoke M (length vs);
               STK = rev vs @ Addr a # stk; xcp = None\<rbrakk> \<Longrightarrow> ?concl A n a' xs pc stk loc`
  note bisim1 = `P,A,n,h \<turnstile> (a', xs) \<leftrightarrow> (STK, loc, pc, xcp)`
  note call = `call (a'\<lfloor>i\<rceil> := e) = \<lfloor>(a, M, vs)\<rfloor>`
  note ins = `compE2 (A\<lfloor>i\<rceil> := e) ! pc = Invoke M (length vs)`
  show ?case
  proof(cases "is_val a'")
    case False
    with bisim1 call have "pc < length (compE2 A)" by(auto intro: bisim1_call_pcD)
    with call ins False IH1 `bsok i n` `bsok e n` `STK = rev vs @ Addr a # stk` `xcp = None` show ?thesis
      by(auto intro: bisim1_bisims1.bisim1AAss1)
  next
    case True
    then obtain v where [simp]: "a' = Val v" by auto
    from bisim1 have "pc \<le> length (compE2 A)" by(auto dest: bisim1_pc_length_compE2)
    moreover {
      assume pc: "pc < length (compE2 A)"
      with bisim1 ins have False by(auto dest: bisim_Val_pc_not_Invoke simp add: nth_append) }
    ultimately have [simp]: "pc = length (compE2 A)" by(cases "pc < length (compE2 A)") auto
    with ins have False by(simp)
    thus ?thesis ..
  qed
next
  case (bisim1AAss2 i n i' xs STK loc pc xcp A e v)
  note IH2 = `\<And>stk. \<lbrakk>call i' = \<lfloor>(a, M, vs)\<rfloor>; compE2 i ! pc = Invoke M (length vs);
                   STK = rev vs @ Addr a # stk; xcp = None\<rbrakk> \<Longrightarrow> ?concl i n i' xs pc stk loc`
  note bisim2 = `P,i,n,h \<turnstile> (i', xs) \<leftrightarrow> (STK, loc, pc, xcp)`
  note call = `call (Val v\<lfloor>i'\<rceil> := e) = \<lfloor>(a, M, vs)\<rfloor>`
  note ins = `compE2 (A\<lfloor>i\<rceil> := e) ! (length (compE2 A) + pc) = Invoke M (length vs)`
  note stk = `STK @ [v] = rev vs @ Addr a # stk`
  show ?case
  proof(cases "is_val i'")
    case False
    with bisim2 call have pc: "pc < length (compE2 i)" by(auto intro: bisim1_call_pcD)
    with ins have ins': "compE2 i ! pc = Invoke M (length vs)" by(simp)
    from bisim1_Invoke_stkD[OF bisim2[unfolded `xcp = None`] pc this]
    obtain vs' v' stk' where [simp]: "STK = vs' @ v' # stk'" and "length vs' = length vs" by auto
    with stk have [simp]: "vs' = rev vs" "v' = Addr a" "stk = stk' @ [v]" by auto
    from IH2[of stk'] ins' pc False `bsok A n` `bsok e n` `xcp = None` call show ?thesis
      by(auto dest: bisim1_bisims1.bisim1AAss2)
  next
    case True
    then obtain v where [simp]: "i' = Val v" by auto
    from bisim2 have "pc \<le> length (compE2 i)" by(auto dest: bisim1_pc_length_compE2)
    moreover {
      assume pc: "pc < length (compE2 i)"
      with bisim2 ins have False by(auto dest: bisim_Val_pc_not_Invoke simp add: nth_append) }
    ultimately have [simp]: "pc = length (compE2 i)" by(cases "pc < length (compE2 i)") auto
    with ins have False by(simp)
    thus ?thesis ..
  qed
next
  case (bisim1AAss3 e n e' xs STK loc pc xcp i A v v')
  note IH2 = `\<And>stk. \<lbrakk>call e' = \<lfloor>(a, M, vs)\<rfloor>; compE2 e ! pc = Invoke M (length vs);
                     STK = rev vs @ Addr a # stk; xcp = None\<rbrakk> \<Longrightarrow> ?concl e n e' xs pc stk loc`
  note bisim3 = `P,e,n,h \<turnstile> (e', xs) \<leftrightarrow> (STK, loc, pc, xcp)`
  note call = `call (Val v\<lfloor>Val v'\<rceil> := e') = \<lfloor>(a, M, vs)\<rfloor>`
  note ins = `compE2 (i\<lfloor>A\<rceil> := e) ! (length (compE2 i) + length (compE2 A) + pc) = Invoke M (length vs)`
  note stk = `STK @ [v', v] = rev vs @ Addr a # stk`
  from call bisim3 have pc: "pc < length (compE2 e)" by(auto intro: bisim1_call_pcD)
  with ins have ins': "compE2 e ! pc = Invoke M (length vs)" by(simp)
  from bisim1_Invoke_stkD[OF bisim3[unfolded `xcp = None`] pc this]
  obtain vs' v'' stk' where [simp]: "STK = vs' @ v'' # stk'" and "length vs' = length vs" by auto
  with stk have [simp]: "vs' = rev vs" "v'' = Addr a" "stk = stk' @ [v', v]" by auto
  from IH2[of stk'] ins' pc `bsok A n` `bsok i n` `xcp = None` call show ?case
    by(auto dest: bisim1_bisims1.bisim1AAss3)
next
  case bisim1AAssThrow1 thus ?case by simp
next
  case bisim1AAssThrow2 thus ?case by simp
next
  case bisim1AAssThrow3 thus ?case by simp
next
  case bisim1AAssBounds thus ?case by simp
next
  case bisim1AAssNull thus ?case by simp
next
  case bisim1AAssStore thus ?case by simp
next
  case bisim1AAss4 thus ?case by simp
next
  case bisim1ALength thus ?case
    by(auto split: split_if_asm dest: bisim1_pc_length_compE2 intro: bisim1_bisims1.bisim1ALength)
next
  case bisim1ALengthNull thus ?case by simp
next
  case bisim1ALengthThrow thus ?case by simp
next
next
  case bisim1FAcc thus ?case
    by(auto split: split_if_asm dest: bisim1_pc_length_compE2 intro: bisim1_bisims1.bisim1FAcc)
next
  case bisim1FAccNull thus ?case by simp
next
  case bisim1FAccThrow thus ?case by simp
next
  case (bisim1FAss1 e1 n e' xs STK loc pc xcp e2 F D)
  note IH1 = `\<lbrakk>call e' = \<lfloor>(a, M, vs)\<rfloor>; compE2 e1 ! pc = Invoke M (length vs);
               STK = rev vs @ Addr a # stk; xcp = None\<rbrakk> \<Longrightarrow> ?concl e1 n e' xs pc stk loc`
  note bisim1 = `P,e1,n,h \<turnstile> (e', xs) \<leftrightarrow> (STK, loc, pc, xcp)`
  note call = `call (e'\<bullet>F{D} := e2) = \<lfloor>(a, M, vs)\<rfloor>`
  note ins = `compE2 (e1\<bullet>F{D} := e2) ! pc = Invoke M (length vs)`
  show ?case
  proof(cases "is_val e'")
    case False
    with bisim1 call have "pc < length (compE2 e1)" by(auto intro: bisim1_call_pcD)
    with call ins False IH1 `bsok e2 n` `STK = rev vs @ Addr a # stk` `xcp = None` show ?thesis
      by(auto intro: bisim1_bisims1.bisim1FAss1)
  next
    case True
    then obtain v where [simp]: "e' = Val v" by auto
    from bisim1 have "pc \<le> length (compE2 e1)" by(auto dest: bisim1_pc_length_compE2)
    moreover {
      assume pc: "pc < length (compE2 e1)"
      with bisim1 ins have False by(auto dest: bisim_Val_pc_not_Invoke simp add: nth_append) }
    ultimately have [simp]: "pc = length (compE2 e1)" by(cases "pc < length (compE2 e1)") auto
    with ins have False by(simp)
    thus ?thesis ..
  qed
next
  case (bisim1FAss2 e2 n e' xs STK loc pc xcp e1 F D v1)
  note IH2 = `\<And>stk. \<lbrakk>call e' = \<lfloor>(a, M, vs)\<rfloor>; compE2 e2 ! pc = Invoke M (length vs);
                     STK = rev vs @ Addr a # stk; xcp = None\<rbrakk> \<Longrightarrow> ?concl e2 n e' xs pc stk loc`
  note bisim2 = `P,e2,n,h \<turnstile> (e', xs) \<leftrightarrow> (STK, loc, pc, xcp)`
  note call = `call (Val v1\<bullet>F{D} := e') = \<lfloor>(a, M, vs)\<rfloor>`
  note ins = `compE2 (e1\<bullet>F{D} := e2) ! (length (compE2 e1) + pc) = Invoke M (length vs)`
  note stk = `STK @ [v1] = rev vs @ Addr a # stk`
  from call bisim2 have pc: "pc < length (compE2 e2)" by(auto intro: bisim1_call_pcD)
  with ins have ins': "compE2 e2 ! pc = Invoke M (length vs)" by(simp)
  from bisim1_Invoke_stkD[OF bisim2[unfolded `xcp = None`] pc this]
  obtain vs' v stk' where [simp]: "STK = vs' @ v # stk'" and "length vs' = length vs" by auto
  with stk have [simp]: "vs' = rev vs" "v = Addr a" "stk = stk' @ [v1]" by auto
  from IH2[of stk'] ins' pc `bsok e1 n` `xcp = None` call show ?case
    by(auto dest: bisim1_bisims1.bisim1FAss2)
next
  case bisim1FAssThrow1 thus ?case by simp
next
  case bisim1FAssThrow2 thus ?case by simp
next
  case bisim1FAssNull thus ?case by simp
next
  case bisim1FAss3 thus ?case by simp
next
  case (bisim1Call1 obj n obj' xs STK loc pc xcp ps M')
  note IH1 = `\<lbrakk>call obj' = \<lfloor>(a, M, vs)\<rfloor>; compE2 obj ! pc = Invoke M (length vs);
              STK = rev vs @ Addr a # stk; xcp = None\<rbrakk> \<Longrightarrow> ?concl obj n obj' xs pc stk loc`
  note bisim1 = `P,obj,n,h \<turnstile> (obj', xs) \<leftrightarrow> (STK, loc, pc, xcp)`
  note call = `call (obj'\<bullet>M'(ps)) = \<lfloor>(a, M, vs)\<rfloor>`
  note ins = `compE2 (obj\<bullet>M'(ps)) ! pc = Invoke M (length vs)`
  note stk = `STK = rev vs @ Addr a # stk`
  note xcp = `xcp = None`
  show ?case
  proof(cases "is_val obj'")
    case False
    with call bisim1 have "pc < length (compE2 obj)" by(auto intro: bisim1_call_pcD)
    with call False ins IH1 `bsoks ps n` False stk xcp show ?thesis
      by(auto intro: bisim1_bisims1.bisim1Call1)
  next
    case True
    then obtain v' where [simp]: "obj' = Val v'" by auto
    from bisim1 have "pc \<le> length (compE2 obj)" by(auto dest: bisim1_pc_length_compE2)
    moreover {
      assume pc: "pc < length (compE2 obj)"
      with bisim1 ins have False by(auto dest: bisim_Val_pc_not_Invoke simp add: nth_append) }
    ultimately have [simp]: "pc = length (compE2 obj)" by(cases "pc < length (compE2 obj)") auto
    with ins have [simp]: "ps = []" "M' = M" "vs = []"
      by(auto simp add: nth_append split: split_if_asm)(auto simp add: neq_Nil_conv nth_append)
    with stk have [simp]: "STK = Addr a # stk" by simp
    from bisim1 have [simp]: "v' = Addr a" "stk = []" "xs = loc"
      by(auto dest: bisim1_pc_length_compE2D bisim_Val_loc_eq_xcp_None)
    from `bsok obj n` have "bsok (obj\<bullet>M([])) n" by simp
    from bisim1Val2[OF this, of P h _ loc] show ?thesis by(auto simp add: is_val_iff)
  qed
next
  case (bisim1CallParams ps n ps' xs STK loc pc xcp obj M' v')
  note IH2 = `\<And>stk. \<lbrakk>calls ps' = \<lfloor>(a, M, vs)\<rfloor>; compEs2 ps ! pc = Invoke M (length vs);
                     STK = rev vs @ Addr a # stk; xcp = None\<rbrakk> \<Longrightarrow> ?concls ps n ps' xs pc stk loc`
  note bisim = `P,ps,n,h \<turnstile> (ps', xs) [\<leftrightarrow>] (STK, loc, pc, xcp)`
  note call = `call (Val v'\<bullet>M'(ps')) = \<lfloor>(a, M, vs)\<rfloor>`
  note ins = `compE2 (obj\<bullet>M'(ps)) ! (length (compE2 obj) + pc) = Invoke M (length vs)`
  note stk = `STK @ [v'] = rev vs @ Addr a # stk`
  note xcp = `xcp = None`
  from call show ?case
  proof(cases rule: call_callE)
    case CallObj thus ?thesis by simp
  next
    case (CallParams v'')
    hence [simp]: "v'' = v'" and call': "calls ps' = \<lfloor>(a, M, vs)\<rfloor>" by simp_all
    from bisim call' have pc: "pc < length (compEs2 ps)" by(rule bisims1_calls_pcD)
    with ins have ins': "compEs2 ps ! pc = Invoke M (length vs)" by(simp add: nth_append)
    from bisims1_Invoke_stkD[OF bisim[unfolded xcp] pc this]
    obtain vs' v''' stk' where [simp]: "STK = vs' @ v''' # stk'" and "length vs' = length vs" by auto
    with stk have [simp]: "vs' = rev vs" "v''' = Addr a" "stk = stk' @ [v']" by auto
    with IH2[of stk'] call' ins xcp pc
    have "P,ps,n,h \<turnstile> (inline_calls (Val v) (fst (clearInitBlocks ps' xs)), snd (clearInitBlocks ps' xs))
                [\<leftrightarrow>] (v # stk', loc, Suc pc, None)" by auto
    hence "P,obj\<bullet>M'(ps),n,h \<turnstile> (Val v'\<bullet>M'(inline_calls (Val v) (fst (clearInitBlocks ps' xs))), snd (clearInitBlocks ps' xs))
                           \<leftrightarrow> ((v # stk') @ [v'], loc, length (compE2 obj) + Suc pc, None)" using `bsok obj n`
      by(rule bisim1_bisims1.bisim1CallParams)
    thus ?thesis using call' by(auto simp add: is_vals_conv)
  next
    case Call
    hence [simp]: "v' = Addr a" "M' = M" "ps' = map Val vs" by auto
    from bisim have "pc \<le> length (compEs2 ps)" by(auto dest: bisims1_pc_length_compEs2)
    moreover {
      assume pc: "pc < length (compEs2 ps)"
      with bisim ins have False by(auto dest: bisims_Val_pc_not_Invoke simp add: nth_append) }
    ultimately have [simp]: "pc = length (compEs2 ps)" by(cases "pc < length (compEs2 ps)") auto
    from bisim have [simp]: "STK = rev vs" "xs = loc" by(auto dest: bisims1_Val_length_compEs2D)
    with `bsok obj n` `bsoks ps n`
    have "P,obj\<bullet>M(ps),n,h \<turnstile> (Val v, loc) \<leftrightarrow> ([v], loc, length (compE2 (obj\<bullet>M(ps))), None)" by-(rule bisim1Val2, auto)
    thus ?thesis using stk by(auto)
  qed
next
  case bisim1CallThrowObj thus ?case by simp
next
  case bisim1CallThrowParams thus ?case by simp
next 
  case bisim1CallThrow thus ?case by simp
next
  case bisim1BlockSome1 thus ?case by simp
next
  case bisim1BlockSome2 thus ?case by simp
next
  case bisim1BlockSome3 thus ?case
    by(auto intro: bisim1_bisims1.bisim1BlockSome4)
next
  case bisim1BlockSome4 thus ?case
    by(auto intro: bisim1_bisims1.bisim1BlockSome4)
next
  case bisim1BlockThrowSome thus ?case by simp
next
  case bisim1BlockNone thus ?case
    by(auto intro: bisim1_bisims1.bisim1BlockNone)
next
  case bisim1BlockThrowNone thus ?case by simp
next
  case bisim1Sync1 thus ?case
    by(auto split: split_if_asm dest: bisim1_pc_length_compE2 intro: bisim1_bisims1.bisim1Sync1)
next
  case bisim1Sync2 thus ?case by simp
next
  case bisim1Sync3 thus ?case by simp
next
  case bisim1Sync4 thus ?case
    by(fastsimp split: split_if_asm dest: bisim1_pc_length_compE2 bisim1_bisims1.bisim1Sync4)
next
  case bisim1Sync5 thus ?case by simp
next
  case bisim1Sync6 thus ?case by simp
next
  case bisim1Sync7 thus ?case by simp
next
  case bisim1Sync8 thus ?case by simp
next
  case bisim1Sync9 thus ?case by simp
next
  case bisim1Sync10 thus ?case by simp
next
  case bisim1Sync11 thus ?case by simp
next
  case bisim1Sync12 thus ?case by simp
next
  case bisim1Sync13 thus ?case by simp
next
  case bisim1Sync14 thus ?case by simp
next
  case bisim1Sync15 thus ?case by simp
next
  case bisim1SyncThrow thus ?case by simp
next
  case bisim1Seq1 thus ?case
    by(auto split: split_if_asm dest: bisim1_pc_length_compE2 intro: bisim1_bisims1.bisim1Seq1)
next
  case bisim1SeqThrow1 thus ?case by simp
next
  case bisim1Seq2 thus ?case
    by(auto split: split_if_asm dest: bisim1_pc_length_compE2)(fastsimp dest: bisim1_bisims1.bisim1Seq2)
next
  case bisim1Cond1 thus ?case
    by(auto split: split_if_asm dest: bisim1_pc_length_compE2 intro: bisim1_bisims1.bisim1Cond1)
next
  case (bisim1CondThen e1 n e' xs STK loc pc xcp e e2) thus ?case
    by(auto split: split_if_asm dest: bisim1_pc_length_compE2)
      (fastsimp dest: bisim1_bisims1.bisim1CondThen[where e=e and ?e2.0=e2])
next
  case (bisim1CondElse e2 n e' xs STK loc pc xcp e e1) thus ?case
    by(auto split: split_if_asm dest: bisim1_pc_length_compE2)
      (fastsimp dest: bisim1_bisims1.bisim1CondElse[where e=e and ?e1.0=e1])
next
  case bisim1CondThrow thus ?case by simp
next
  case bisim1While1 thus ?case by simp
next
  case bisim1While3 thus ?case
    by(auto split: split_if_asm dest: bisim1_pc_length_compE2 intro: bisim1_bisims1.bisim1While3)
next
  case bisim1While4 thus ?case
    by(auto split: split_if_asm dest: bisim1_pc_length_compE2)(fastsimp dest: bisim1_bisims1.bisim1While4)
next
  case bisim1While6 thus ?case by simp
next
  case bisim1While7 thus ?case by simp
next
  case bisim1WhileThrow1 thus ?case by simp
next
  case bisim1WhileThrow2 thus ?case by simp
next
  case bisim1Throw1 thus ?case
    by(auto split: split_if_asm dest: bisim1_pc_length_compE2 intro: bisim1_bisims1.bisim1Throw1)
next
  case bisim1Throw2 thus ?case by simp
next
  case bisim1ThrowNull thus ?case by simp
next
  case bisim1ThrowThrow thus ?case by simp
next
  case bisim1Try thus ?case
    by(auto split: split_if_asm dest: bisim1_pc_length_compE2 intro: bisim1_bisims1.bisim1Try)
next
  case bisim1TryCatch1 thus ?case by simp
next
  case bisim1TryCatch2 thus ?case
    by(fastsimp dest: bisim1_bisims1.bisim1TryCatch2)
next
  case bisim1TryFail thus ?case by simp
next
  case bisim1TryCatchThrow thus ?case by simp
next
  case bisims1Nil thus ?case by simp
next
  case (bisims1List1 e n e' xs STK loc pc xcp es)
  note IH1 = `\<lbrakk>call e' = \<lfloor>(a, M, vs)\<rfloor>; compE2 e ! pc = Invoke M (length vs);
               STK = rev vs @ Addr a # stk; xcp = None\<rbrakk> \<Longrightarrow> ?concl e n e' xs pc stk loc`
  note bisim1 = `P,e,n,h \<turnstile> (e', xs) \<leftrightarrow> (STK, loc, pc, xcp)`
  note call = `calls (e' # es) = \<lfloor>(a, M, vs)\<rfloor>`
  note ins = `compEs2 (e # es) ! pc = Invoke M (length vs)`
  note stk = `STK = rev vs @ Addr a # stk`
  note xcp = `xcp = None`
  show ?case
  proof(cases "is_val e'")
    case False
    with bisim1 call have "pc < length (compE2 e)" by(auto intro: bisim1_call_pcD)
    with call ins False IH1 `bsoks es n` stk xcp show ?thesis
      by(auto intro: bisim1_bisims1.bisims1List1)
  next
    case True
    then obtain v where [simp]: "e' = Val v" by auto
    from bisim1 have "pc \<le> length (compE2 e)" by(auto dest: bisim1_pc_length_compE2)
    moreover {
      assume pc: "pc < length (compE2 e)"
      with bisim1 ins have False by(auto dest: bisim_Val_pc_not_Invoke simp add: nth_append) }
    ultimately have [simp]: "pc = length (compE2 e)" by(cases "pc < length (compE2 e)") auto
    with ins call have False by(cases es)(auto)
    thus ?thesis ..
  qed
next
  case (bisims1List2 es n es' xs STK loc pc xcp e v')
  note IH = `\<And>stk. \<lbrakk>calls es' = \<lfloor>(a, M, vs)\<rfloor>; compEs2 es ! pc = Invoke M (length vs);
             STK = rev vs @ Addr a # stk; xcp = None\<rbrakk> \<Longrightarrow> ?concls es n es' xs pc stk loc`
  note call = `calls (Val v' # es') = \<lfloor>(a, M, vs)\<rfloor>`
  note bisim = `P,es,n,h \<turnstile> (es', xs) [\<leftrightarrow>] (STK, loc, pc, xcp)`
  note ins = `compEs2 (e # es) ! (length (compE2 e) + pc) = Invoke M (length vs)`
  from call have call': "calls es' = \<lfloor>(a, M, vs)\<rfloor>" by simp
  with bisim have pc: "pc < length (compEs2 es)" by(rule bisims1_calls_pcD)
  with ins have ins': "compEs2 es ! pc = Invoke M (length vs)" by(simp add: nth_append)
  from  bisims1_Invoke_stkD[OF bisim[unfolded `xcp = None`] pc this]
  obtain vs' v stk' where [simp]: "STK = vs' @ v # stk'" and "length vs' = length vs" by auto
  with `STK @ [v'] = rev vs @ Addr a # stk` have [simp]: "vs' = rev vs" "v = Addr a" "stk = stk' @ [v']" by auto
  from IH[of stk'] call ins `bsok e n` pc `xcp = None` show ?case
    by(auto split: split_if_asm dest: bisim1_bisims1.bisims1List2)
qed


lemma bisim1_fv: "P,e,n,h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, xcp) \<Longrightarrow> fv e' \<subseteq> fv e"
  and bisims1_fvs: "P,es,n,h \<turnstile> (es', xs) [\<leftrightarrow>] (stk,loc,pc,xcp) \<Longrightarrow> fvs es' \<subseteq> fvs es"
apply(induct rule: bisim1_bisims1_inducts_split)
apply(auto)
done


lemma bisim1_syncvars: "\<lbrakk> P,e,n,h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, xcp); syncvars e \<rbrakk> \<Longrightarrow> syncvars e'"
  and bisims1_syncvarss: "\<lbrakk> P,es,n,h \<turnstile> (es', xs) [\<leftrightarrow>] (stk,loc,pc,xcp); syncvarss es \<rbrakk> \<Longrightarrow> syncvarss es'"
apply(induct rule: bisim1_bisims1_inducts_split)
apply(auto dest: bisim1_fv)
done

declare pcs_stack_xlift [simp]

lemma bisim1_Val_\<tau>Red:
  "\<lbrakk> P, E, n, h \<turnstile> (e, xs) \<leftrightarrow> ([v], loc, length (compE2 E), None); n + max_vars e \<le> length xs \<rbrakk> \<Longrightarrow> \<tau>Red P h e xs (Val v) loc"

 and bisims1_Val_\<tau>Reds:
  "\<lbrakk> P, Es, n, h \<turnstile> (es, xs) [\<leftrightarrow>] (rev vs, loc, length (compEs2 Es), None); n + max_varss es \<le> length xs \<rbrakk>
   \<Longrightarrow> \<tau>Reds P h es xs (map Val vs) loc"
proof(induct E n e xs stk\<equiv>"[v]" loc pc\<equiv>"length (compE2 E)" xcp\<equiv>"None::addr option"
         and Es n es xs stk\<equiv>"rev vs" loc pc\<equiv>"length (compEs2 Es)" xcp\<equiv>"None::addr option"
      arbitrary: v and vs rule: bisim1_bisims1_inducts_split)
  case bisim1BlockSome2 thus ?case by(simp (no_asm_use))
next
  case (bisim1BlockSome3 e V e' xs v stk loc pc xcp T val)
  note len = `V + max_vars {V:T=\<lfloor>v\<rfloor>; e'}\<^bsub>False\<^esub> \<le> length xs`
  hence V: "V < length xs" by simp
  note IH = `\<And>val. \<lbrakk>Suc V + max_vars e' \<le> length (xs[V := v]); stk = [val]; pc = length (compE2 e); xcp = None\<rbrakk>
             \<Longrightarrow> \<tau>Red P h e' (xs[V := v]) (Val val) loc`
  with len `Suc (Suc pc) = length (compE2 {V:T=\<lfloor>v\<rfloor>; e}\<^bsub>False\<^esub>)` `stk = [val]` `xcp = None`
  have red: "\<tau>Red P h e' (xs[V := v]) (Val val) loc" by simp
  from `P,e,Suc V,h \<turnstile> (e', xs[V := v]) \<leftrightarrow> (stk, loc, pc, xcp)`
  have lenxs: "length xs = length loc" by(auto dest: bisim1_length_xs)
  show ?case
  proof(cases "e' = Val val \<and> xs[V := v] = loc")
    case True
    thus ?thesis using V
      by(auto intro: \<tau>Red1step Red1BlockSome \<tau>move1BlockRed)
  next
    case False
    with red V have "\<tau>Red P h {V:T=\<lfloor>v\<rfloor>; e'}\<^bsub>False\<^esub> xs {V:T=None; Val val}\<^bsub>False\<^esub> loc"
      by -(erule Block_\<tau>Red_Some, auto)
    thus ?thesis using V lenxs
      by(auto elim!: \<tau>Red_step intro: Red1BlockNone \<tau>move1BlockRed)
  qed    
next
  case (bisim1BlockSome4 e V e' xs stk loc pc xcp T val)
  note len = `V + max_vars {V:T=None; e'}\<^bsub>False\<^esub> \<le> length xs`
  hence V: "V < length xs" by simp
  from `P,e,Suc V,h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, xcp)`
  have lenxs: "length xs = length loc" by(auto dest: bisim1_length_xs)
  note IH = `\<And>v. \<lbrakk>Suc V + max_vars e' \<le> length xs; stk = [v]; pc = length (compE2 e); xcp = None\<rbrakk>
             \<Longrightarrow> \<tau>Red P h e' xs (Val v) loc`
  with len `Suc (Suc pc) = length (compE2 {V:T=\<lfloor>val\<rfloor>; e}\<^bsub>False\<^esub>)`
    `stk = [v]` `xcp = None`
  have "\<tau>Red P h e' xs (Val v) loc" by(simp)
  hence "\<tau>Red P h {V:T=None; e'}\<^bsub>False\<^esub> xs {V:T=None; Val v}\<^bsub>False\<^esub> loc" using V
    by(rule Block_None_\<tau>Red_xt)
  thus ?case using V lenxs by(auto elim!: \<tau>Red_step intro: Red1BlockNone \<tau>move1BlockRed)
next
  case (bisim1BlockNone e V e' xs stk loc pc xcp T)
  note len = `V + max_vars {V:T=None; e'}\<^bsub>False\<^esub> \<le> length xs`
  hence V: "V < length xs" by simp
  from `P,e,Suc V,h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, xcp)`
  have lenxs: "length xs = length loc" by(auto dest: bisim1_length_xs)
  note IH = `\<And>v. \<lbrakk>Suc V + max_vars e' \<le> length xs; stk = [v]; pc = length (compE2 e); xcp = None\<rbrakk>
             \<Longrightarrow> \<tau>Red P h e' xs (Val v) loc`
  with len `pc = length (compE2 {V:T=None; e}\<^bsub>False\<^esub>)` `stk = [v]` `xcp = None`
  have "\<tau>Red P h e' xs (Val v) loc" by(simp)
  hence "\<tau>Red P h {V:T=None; e'}\<^bsub>False\<^esub> xs {V:T=None; Val v}\<^bsub>False\<^esub> loc" using V
    by(rule Block_None_\<tau>Red_xt)
  thus ?case using V lenxs by(auto elim!: \<tau>Red_step intro: Red1BlockNone \<tau>move1BlockRed)
next
  case (bisim1TryCatch2 e2 V e' xs stk loc pc xcp e C)
  note len = `V + max_vars {V:Class C=None; e'}\<^bsub>False\<^esub> \<le> length xs`
  hence V: "V < length xs" by simp
  from `P,e2,Suc V,h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, xcp)`
  have lenxs: "length xs = length loc" by(auto dest: bisim1_length_xs)
  note IH = `\<And>v. \<lbrakk>Suc V + max_vars e' \<le> length xs; stk = [v]; pc = length (compE2 e2); xcp = None\<rbrakk>
             \<Longrightarrow> \<tau>Red P h e' xs (Val v) loc`
  with len `Suc (Suc (length (compE2 e) + pc)) = length (compE2 (try e catch(C V) e2))` `stk = [v]` `xcp = None`
  have "\<tau>Red P h e' xs (Val v) loc" by(simp)
  hence "\<tau>Red P h {V:Class C=None; e'}\<^bsub>False\<^esub> xs {V:Class C=None; Val v}\<^bsub>False\<^esub> loc"
    using V by(rule Block_None_\<tau>Red_xt)
  thus ?case using V lenxs by(auto elim!: \<tau>Red_step intro: Red1BlockNone \<tau>move1BlockRed)
next
  case (bisims1List1 e n e' xs stk loc pc xcp es)
  note bisim = `P,e,n,h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, xcp)`
  with `pc = length (compEs2 (e # es))` have es: "es = []" and pc: "pc = length (compE2 e)"
    by(auto dest: bisim1_pc_length_compE2)
  with bisim obtain val where stk: "stk = [val]" and e': "is_val e' \<Longrightarrow> e' = Val val"
    by(auto dest: bisim1_pc_length_compE2D)
  with es pc bisims1List1 have "\<tau>Red P h e' xs (Val val) loc" by simp
  with stk es `stk = rev vs` show ?case by(auto intro: \<tau>Red_inj_\<tau>Reds)
next
  case (bisims1List2 es n es' xs stk loc pc xcp e v)
  from `stk @ [v] = rev vs` obtain vs' where vs: "vs = v # vs'" by(cases vs) auto
  with bisims1List2 show ?case by(auto intro: \<tau>Reds_cons_\<tau>Reds)
qed(fastsimp intro: \<tau>Red_refl \<tau>Reds_refl dest: bisim1_pc_length_compE2 bisims1_pc_length_compEs2 split: bop.split_asm)+

lemma exec_meth_stk_split:
  "\<lbrakk> P,E,n,h \<turnstile> (e, xs) \<leftrightarrow> (stk, loc, pc, xcp);
     exec_meth (compP2 P) (compE2 E) (stack_xlift (length STK) (compxE2 E 0 0))
                h (stk @ STK, loc, pc, xcp) ta h' (stk', loc', pc', xcp') \<rbrakk>
  \<Longrightarrow> \<exists>stk''. stk' = stk'' @ STK \<and> exec_meth (compP2 P) (compE2 E) (compxE2 E 0 0)
                                             h (stk, loc, pc, xcp) ta h' (stk'', loc', pc', xcp')"
  (is "\<lbrakk> _; ?exec E stk STK loc pc xcp stk' loc' pc' xcp' \<rbrakk> \<Longrightarrow> ?concl E stk STK loc pc xcp stk' loc' pc' xcp'")

  and exec_meth_stk_splits:
  "\<lbrakk> P,Es,n,h \<turnstile> (es,xs) [\<leftrightarrow>] (stk,loc,pc,xcp);
     exec_meth (compP2 P) (compEs2 Es) (stack_xlift (length STK) (compxEs2 Es 0 0)) 
                h (stk @ STK, loc, pc, xcp) ta h' (stk', loc', pc', xcp') \<rbrakk>
  \<Longrightarrow> \<exists>stk''. stk' = stk'' @ STK \<and> exec_meth (compP2 P) (compEs2 Es) (compxEs2 Es 0 0)
                                             h (stk, loc, pc, xcp) ta h' (stk'', loc', pc', xcp')"
  (is "\<lbrakk> _; ?execs Es stk STK loc pc xcp stk' loc' pc' xcp' \<rbrakk> \<Longrightarrow> ?concls Es stk STK loc pc xcp stk' loc' pc' xcp'")
proof(induct arbitrary: stk' loc' pc' xcp' STK and stk' loc' pc' xcp' STK rule: bisim1_bisims1_inducts_split)
  case bisim1Val2 thus ?case by(auto dest: exec_meth_length_compE2_stack_xliftD)
next
  case bisim1New thus ?case by(fastsimp elim: exec_meth.cases intro: exec_meth.intros)
next
  case bisim1NewThrow thus ?case by(fastsimp elim: exec_meth.cases intro: exec_meth.intros)
next
  case (bisim1NewArray e n e' xs stk loc pc xcp T)
  note bisim = `P,e,n,h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, xcp)`
  note IH = `\<And>stk' loc' pc' xcp' STK. ?exec e stk STK loc pc xcp stk' loc' pc' xcp'
             \<Longrightarrow> ?concl e stk STK loc pc xcp stk' loc' pc' xcp'`
  note exec = `?exec (newA T\<lfloor>e\<rceil>) stk STK loc pc xcp stk' loc' pc' xcp'`
  from bisim have pc: "pc \<le> length (compE2 e)" by(rule bisim1_pc_length_compE2)
  show ?case
  proof(cases "pc < length (compE2 e)")
    case True
    with exec have "?exec e stk STK loc pc xcp stk' loc' pc' xcp'"
      by(simp add: compxE2_size_convs)(erule exec_meth_take)
    from IH[OF this] show ?thesis by auto
  next
    case False
    with pc have [simp]: "pc = length (compE2 e)" by simp
    with bisim obtain v where [simp]: "stk = [v]" "xcp = None"
      by(auto dest: dest: bisim1_pc_length_compE2D)
    with exec show ?thesis apply(simp)
      by(erule exec_meth.cases)(auto intro!: exec_meth.intros split: split_if_asm)
  qed
next
  case (bisim1NewArrayThrow e n a xs stk loc pc T)
  note bisim = `P,e,n,h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)`
  note IH = `\<And>stk' loc' pc' xcp' STK. ?exec e stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'
             \<Longrightarrow> ?concl e stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'`
  note exec = `?exec (newA T\<lfloor>e\<rceil>) stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'`
  from bisim have pc: "pc < length (compE2 e)" and [simp]: "xs = loc"
    by(auto dest: bisim1_ThrowD)
  from exec have "?exec e stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'"
    by(simp)(erule exec_meth_take[OF _ pc])
  from IH[OF this] show ?case by(auto)
next
  case bisim1NewArrayFail thus ?case
    by(auto elim!: exec_meth.cases dest: match_ex_table_pcsD simp add: stack_xlift_compxEs2 stack_xlift_compxE2)
next
  case bisim1NewArrayNegative thus ?case
    by(auto elim!: exec_meth.cases dest: match_ex_table_pcsD simp add: stack_xlift_compxEs2 stack_xlift_compxE2)
next
  case (bisim1Cast e n e' xs stk loc pc xcp T)
  note bisim = `P,e,n,h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, xcp)`
  note IH = `\<And>stk' loc' pc' xcp' STK. ?exec e stk STK loc pc xcp stk' loc' pc' xcp'
             \<Longrightarrow> ?concl e stk STK loc pc xcp stk' loc' pc' xcp'`
  note exec = `?exec (Cast T e) stk STK loc pc xcp stk' loc' pc' xcp'`
  from bisim have pc: "pc \<le> length (compE2 e)" by(rule bisim1_pc_length_compE2)
  show ?case
  proof(cases "pc < length (compE2 e)")
    case True
    with exec have "?exec e stk STK loc pc xcp stk' loc' pc' xcp'"
      by(simp add: compxE2_size_convs)(erule exec_meth_take)
    from IH[OF this] show ?thesis by auto
  next
    case False
    with pc have [simp]: "pc = length (compE2 e)" by simp
    with bisim obtain v where [simp]: "stk = [v]" "xcp = None"
      by(auto dest: dest: bisim1_pc_length_compE2D)
    with exec show ?thesis apply(simp)
      by(erule exec_meth.cases)(auto intro!: exec_meth.intros split: split_if_asm)
  qed
next
  case (bisim1CastThrow e n a xs stk loc pc T)
  note bisim = `P,e,n,h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)`
  note IH = `\<And>stk' loc' pc' xcp' STK. ?exec e stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'
             \<Longrightarrow> ?concl e stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'`
  note exec = `?exec (Cast T e) stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'`
  from bisim have pc: "pc < length (compE2 e)" and [simp]: "xs = loc"
    by(auto dest: bisim1_ThrowD)
  from exec have "?exec e stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'"
    by(simp)(erule exec_meth_take[OF _ pc])
  from IH[OF this] show ?case by(auto)
next
  case bisim1CastFail thus ?case
    by(auto elim!: exec_meth.cases dest: match_ex_table_pcsD simp add: stack_xlift_compxEs2 stack_xlift_compxE2)
next
  case bisim1Val thus ?case by(fastsimp elim: exec_meth.cases intro: exec_meth.intros)
next
  case bisim1Var thus ?case by(fastsimp elim: exec_meth.cases intro: exec_meth.intros)
next
  case (bisim1BinOp1 e1 n e1' xs stk loc pc xcp e2 bop)
  note IH1 = `\<And>stk' loc' pc' xcp' STK. ?exec e1 stk STK loc pc xcp stk' loc' pc' xcp'
             \<Longrightarrow> ?concl e1 stk STK loc pc xcp stk' loc' pc' xcp'`
  note IH2 = `\<And>xs stk' loc' pc' xcp' STK. ?exec e2 [] STK xs 0 None stk' loc' pc' xcp'
             \<Longrightarrow> ?concl e2 [] STK xs 0 None stk' loc' pc' xcp'`
  note bisim1 = `P,e1,n,h \<turnstile> (e1', xs) \<leftrightarrow> (stk, loc, pc, xcp)`
  note bisim2 = `P,e2,n,h \<turnstile> (e2, loc) \<leftrightarrow> ([], loc, 0, None)`
  note exec = `?exec (e1 \<guillemotleft>bop\<guillemotright> e2) stk STK loc pc xcp stk' loc' pc' xcp'`
  from bisim1 have pc: "pc \<le> length (compE2 e1)" by(rule bisim1_pc_length_compE2)
  show ?case
  proof(cases "pc < length (compE2 e1)")
    case True
    with exec have "?exec e1 stk STK loc pc xcp stk' loc' pc' xcp'"
      by(simp add: compxE2_size_convs)(erule exec_meth_take_xt)
    from IH1[OF this] show ?thesis by auto
  next
    case False
    with pc have pc: "pc = length (compE2 e1)" by simp
    with exec have "pc' \<ge> length (compE2 e1)"
      by(simp add: compxE2_size_convs stack_xlift_compxE2)(auto split: bop.splits elim!: exec_meth_drop_xt_pc)
    then obtain PC where PC: "pc' = PC + length (compE2 e1)"
      by -(rule_tac PC="pc' - length (compE2 e1)" in that, simp)
    from pc bisim1 obtain v where "stk = [v]" "xcp = None" by(auto dest: bisim1_pc_length_compE2D)
    with exec pc have "exec_meth (compP2 P) (compE2 e1 @ compE2 e2)
   (stack_xlift (length STK) (compxE2 e1 0 0 @ compxE2 e2 (length (compE2 e1)) (Suc 0))) h (stk @ STK, loc, length (compE2 e1) + 0, xcp) ta h' (stk', loc', pc', xcp')"
      by-(rule exec_meth_take, auto)
    hence "?exec e2 [] (v # STK) loc 0 None stk' loc' (pc' - length (compE2 e1)) xcp'"
      using `stk = [v]` `xcp = None`
      by -(rule exec_meth_drop_xt, auto simp add: stack_xlift_compxE2 shift_compxE2)
    from IH2[OF this] PC obtain stk'' where stk': "stk' = stk'' @ v # STK"
      and "exec_meth (compP2 P) (compE2 e2) (compxE2 e2 0 0) h ([], loc, 0, None) ta h' (stk'', loc', PC, xcp')" by auto
    hence "exec_meth (compP2 P) ((compE2 e1 @ compE2 e2) @ (case bop of Eq \<Rightarrow> [CmpEq] | Add \<Rightarrow> [IAdd]))
        (compxE2 e1 0 0 @ shift (length (compE2 e1)) (stack_xlift (length [v]) (compxE2 e2 0 0))) h
        ([] @ [v], loc, length (compE2 e1) + 0, None) ta h' (stk'' @ [v], loc', length (compE2 e1) + PC, xcp')"
      apply -
      apply(rule exec_meth_append)
      apply(rule append_exec_meth_xt)
      apply(erule exec_meth_stk_offer)
      by(auto)
    thus ?thesis using `stk = [v]` `xcp = None` stk' pc PC
      by(clarsimp simp add: shift_compxE2 stack_xlift_compxE2 add_ac)
  qed
next
  case (bisim1BinOp2 e2 n e2' xs stk loc pc xcp e1 bop v1)
  note IH2 = `\<And>stk' loc' pc' xcp' STK. ?exec e2 stk STK loc pc xcp stk' loc' pc' xcp'
             \<Longrightarrow> ?concl e2 stk STK loc pc xcp stk' loc' pc' xcp'`
  note bisim1 = `P,e1,n,h \<turnstile> (e1, xs) \<leftrightarrow> ([], xs, 0, None)`
  note bisim2 = `P,e2,n,h \<turnstile> (e2', xs) \<leftrightarrow> (stk, loc, pc, xcp)`
  note exec = `?exec (e1 \<guillemotleft>bop\<guillemotright> e2) (stk @ [v1]) STK loc (length (compE2 e1) + pc) xcp stk' loc' pc' xcp'`
  from bisim2 have pc: "pc \<le> length (compE2 e2)" by(rule bisim1_pc_length_compE2)
  show ?case
  proof(cases "pc < length (compE2 e2)")
    case True
    from exec have "exec_meth (compP2 P) ((compE2 e1 @ compE2 e2) @ (case bop of Eq \<Rightarrow> [CmpEq] | Add \<Rightarrow> [IAdd]))
      (stack_xlift (length STK) (compxE2 e1 0 0) @ shift (length (compE2 e1)) (stack_xlift (length STK) (compxE2 e2 0 (Suc 0))))
      h (stk @ v1 # STK, loc, length (compE2 e1) + pc, xcp) ta h' (stk', loc', pc', xcp')" by(simp add: compxE2_size_convs)
    hence exec': "exec_meth (compP2 P) (compE2 e1 @ compE2 e2) (stack_xlift (length STK) (compxE2 e1 0 0) @
      shift (length (compE2 e1)) (stack_xlift (length STK) (compxE2 e2 0 (Suc 0))))
      h (stk @ v1 # STK, loc, length (compE2 e1) + pc, xcp) ta h' (stk', loc', pc', xcp')"
      by(rule exec_meth_take)(simp add: True)
    hence "exec_meth (compP2 P) (compE2 e2) (stack_xlift (length STK) (compxE2 e2 0 (Suc 0)))
      h (stk @ v1 # STK, loc, pc, xcp) ta h' (stk', loc', pc' - length (compE2 e1), xcp')"
      by(rule exec_meth_drop_xt)(auto simp add: stack_xlift_compxE2)
    hence "?exec e2 stk (v1 # STK) loc pc xcp stk' loc' (pc' - length (compE2 e1)) xcp'"
      by(simp add: compxE2_stack_xlift_convs)
    from IH2[OF this] obtain stk'' where stk': "stk' = stk'' @ v1 # STK"
      and exec'': "exec_meth (compP2 P) (compE2 e2) (compxE2 e2 0 0) h (stk, loc, pc, xcp) ta h' (stk'', loc', pc' - length (compE2 e1), xcp')" by blast
    from exec'' have "exec_meth (compP2 P) (compE2 e2) (stack_xlift (length [v1]) (compxE2 e2 0 0)) h (stk @ [v1], loc, pc, xcp)
      ta h' (stk'' @ [v1], loc', pc' - length (compE2 e1), xcp')"
      by(rule exec_meth_stk_offer)
    hence "exec_meth (compP2 P) (compE2 e1 @ compE2 e2) (compxE2 e1 0 0 @ shift (length (compE2 e1)) (stack_xlift (length [v1]) (compxE2 e2 0 0))) h (stk @ [v1], loc, length (compE2 e1) + pc, xcp)
      ta h' (stk'' @ [v1], loc', length (compE2 e1) + (pc' - length (compE2 e1)), xcp')"
      by(rule append_exec_meth_xt) auto
    hence "exec_meth (compP2 P) ((compE2 e1 @ compE2 e2) @ (case bop of Eq \<Rightarrow> [CmpEq] | Add \<Rightarrow> [IAdd])) (compxE2 e1 0 0 @ shift (length (compE2 e1)) (stack_xlift (length [v1]) (compxE2 e2 0 0))) h (stk @ [v1], loc, length (compE2 e1) + pc, xcp)
      ta h' (stk'' @ [v1], loc', length (compE2 e1) + (pc' - length (compE2 e1)), xcp')"
      by(rule exec_meth_append)
    moreover from exec' have "pc' \<ge> length (compE2 e1)"
      by(rule exec_meth_drop_xt_pc)(auto simp add: stack_xlift_compxE2)
    ultimately show ?thesis using stk' by(simp add: stack_xlift_compxE2 shift_compxE2)
  next
    case False
    with pc have pc: "pc = length (compE2 e2)" by simp
    with bisim2 obtain v2 where [simp]: "stk = [v2]" "xcp = None"
      by(auto dest: dest: bisim1_pc_length_compE2D)
    with exec pc show ?thesis apply(simp)
      by(erule exec_meth.cases)(auto split: bop.splits intro!: exec_meth.intros)
  qed
next
  case (bisim1BinOpThrow1 e1 n a xs stk loc pc e2 bop)
  note bisim1 = `P,e1,n,h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)`
  note IH1 = `\<And>stk' loc' pc' xcp' STK. ?exec e1 stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'
             \<Longrightarrow> ?concl e1 stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'`
  note exec = `?exec (e1 \<guillemotleft>bop\<guillemotright> e2) stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'`
  from bisim1 have pc: "pc < length (compE2 e1)" and [simp]: "xs = loc"
    by(auto dest: bisim1_ThrowD)
  from exec have "exec_meth (compP2 P) (compE2 e1 @ (compE2 e2 @ (case bop of Eq \<Rightarrow> [CmpEq] | Add \<Rightarrow> [IAdd])))
     (stack_xlift (length STK) (compxE2 e1 0 0) @ shift (length (compE2 e1)) (stack_xlift (length STK) (compxE2 e2 0 (Suc 0))))
     h (stk @ STK, loc, pc, \<lfloor>a\<rfloor>) ta h' (stk', loc', pc', xcp')" by(simp add: compxE2_size_convs)
  hence "?exec e1 stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'"
    by(rule exec_meth_take_xt)(rule pc)
  from IH1[OF this] show ?case by(auto)
next
  case (bisim1BinOpThrow2 e2 n a xs stk loc pc e1 bop v1)
  note bisim2 = `P,e2,n,h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)`
  note IH2 = `\<And>stk' loc' pc' xcp' STK. ?exec e2 stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'
             \<Longrightarrow> ?concl e2 stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'`
  note exec = `?exec (e1 \<guillemotleft>bop\<guillemotright> e2) (stk @ [v1]) STK loc (length (compE2 e1) + pc) \<lfloor>a\<rfloor> stk' loc' pc' xcp'`
  from bisim2 have pc: "pc < length (compE2 e2)" and [simp]: "xs = loc"
    by(auto dest: bisim1_ThrowD)
  from exec have "exec_meth (compP2 P) ((compE2 e1 @ compE2 e2) @ (case bop of Eq \<Rightarrow> [CmpEq] | Add \<Rightarrow> [IAdd]))
     (stack_xlift (length STK) (compxE2 e1 0 0) @ shift (length (compE2 e1)) (stack_xlift (length STK) (compxE2 e2 0 (Suc 0))))
     h (stk @ v1 # STK, loc, length (compE2 e1) + pc, \<lfloor>a\<rfloor>) ta h' (stk', loc', pc', xcp')"
    by(simp add: compxE2_size_convs)
  hence exec': "exec_meth (compP2 P) (compE2 e1 @ compE2 e2)
     (stack_xlift (length STK) (compxE2 e1 0 0) @ shift (length (compE2 e1)) (stack_xlift (length STK) (compxE2 e2 0 (Suc 0))))
     h (stk @ v1 # STK, loc, length (compE2 e1) + pc, \<lfloor>a\<rfloor>) ta h' (stk', loc', pc', xcp')"
    by(rule exec_meth_take)(simp add: pc)
  hence "exec_meth (compP2 P) (compE2 e2) (stack_xlift (length STK) (compxE2 e2 0 (Suc 0)))
     h (stk @ v1 # STK, loc, pc, \<lfloor>a\<rfloor>) ta h' (stk', loc', pc' - length (compE2 e1), xcp')"
    by(rule exec_meth_drop_xt)(auto simp add: stack_xlift_compxE2)
  hence "?exec e2 stk (v1 # STK) loc pc \<lfloor>a\<rfloor> stk' loc' (pc' - length (compE2 e1)) xcp'"
    by(simp add: compxE2_stack_xlift_convs)
  from IH2[OF this] obtain stk'' where stk': "stk' = stk'' @ v1 # STK" and
    exec'': "exec_meth (compP2 P) (compE2 e2) (compxE2 e2 0 0) h (stk, loc, pc, \<lfloor>a\<rfloor>) ta h' (stk'', loc', pc' - length (compE2 e1), xcp')" by blast
  from exec'' have "exec_meth (compP2 P) (compE2 e2) (stack_xlift (length [v1]) (compxE2 e2 0 0)) h (stk @ [v1], loc, pc, \<lfloor>a\<rfloor>)
      ta h' (stk'' @ [v1], loc', pc' - length (compE2 e1), xcp')"
    by(rule exec_meth_stk_offer)
  hence "exec_meth (compP2 P) (compE2 e1 @ compE2 e2) (compxE2 e1 0 0 @ shift (length (compE2 e1)) (stack_xlift (length [v1]) (compxE2 e2 0 0))) h (stk @ [v1], loc, length (compE2 e1) + pc, \<lfloor>a\<rfloor>)
      ta h' (stk'' @ [v1], loc', length (compE2 e1) + (pc' - length (compE2 e1)), xcp')"
    by(rule append_exec_meth_xt)(auto)
  hence "exec_meth (compP2 P) ((compE2 e1 @ compE2 e2) @ (case bop of Eq \<Rightarrow> [CmpEq] | Add \<Rightarrow> [IAdd])) (compxE2 e1 0 0 @ shift (length (compE2 e1)) (stack_xlift (length [v1]) (compxE2 e2 0 0))) h (stk @ [v1], loc, length (compE2 e1) + pc, \<lfloor>a\<rfloor>)
      ta h' (stk'' @ [v1], loc', length (compE2 e1) + (pc' - length (compE2 e1)), xcp')"
    by(rule exec_meth_append)
  moreover from exec' have pc': "pc' \<ge> length (compE2 e1)"
    by(rule exec_meth_drop_xt_pc)(auto simp add: stack_xlift_compxE2)
  ultimately show ?case using stk' by(auto simp add: stack_xlift_compxE2 shift_compxE2)
next
  case (bisim1LAss1 e n e' xs stk loc pc xcp V)
  note bisim = `P,e,n,h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, xcp)`
  note IH = `\<And>stk' loc' pc' xcp' STK. ?exec e stk STK loc pc xcp stk' loc' pc' xcp'
             \<Longrightarrow> ?concl e stk STK loc pc xcp stk' loc' pc' xcp'`
  note exec = `?exec (V := e) stk STK loc pc xcp stk' loc' pc' xcp'`
  from bisim have pc: "pc \<le> length (compE2 e)" by(rule bisim1_pc_length_compE2)
  show ?case
  proof(cases "pc < length (compE2 e)")
    case True
    with exec have "?exec e stk STK loc pc xcp stk' loc' pc' xcp'"
      by(simp add: compxE2_size_convs)(erule exec_meth_take)
    from IH[OF this] show ?thesis by auto
  next
    case False
    with pc have [simp]: "pc = length (compE2 e)" by simp
    with bisim obtain v where [simp]: "stk = [v]" "xcp = None"
      by(auto dest: dest: bisim1_pc_length_compE2D)
    with exec show ?thesis apply(simp)
      by(erule exec_meth.cases)(auto intro!: exec_meth.intros)
  qed
next
  case (bisim1LAss2 e n xs V)
  thus ?case by(fastsimp elim: exec_meth.cases intro: exec_meth.intros)
next
  case (bisim1LAssThrow e n a xs stk loc pc V)
  note bisim = `P,e,n,h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)`
  note IH = `\<And>stk' loc' pc' xcp' STK. ?exec e stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'
             \<Longrightarrow> ?concl e stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'`
  note exec = `?exec (V := e) stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'`
  from bisim have pc: "pc < length (compE2 e)" and [simp]: "xs = loc"
    by(auto dest: bisim1_ThrowD)
  from exec have "?exec e stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'"
    by(simp)(erule exec_meth_take[OF _ pc])
  from IH[OF this] show ?case by(auto)
next
  case (bisim1AAcc1 a n a' xs stk loc pc xcp i)
  note IH1 = `\<And>stk' loc' pc' xcp' STK. ?exec a stk STK loc pc xcp stk' loc' pc' xcp'
             \<Longrightarrow> ?concl a stk STK loc pc xcp stk' loc' pc' xcp'`
  note IH2 = `\<And>xs stk' loc' pc' xcp' STK. ?exec i [] STK xs 0 None stk' loc' pc' xcp'
             \<Longrightarrow> ?concl i [] STK xs 0 None stk' loc' pc' xcp'`
  note bisim1 = `P,a,n,h \<turnstile> (a', xs) \<leftrightarrow> (stk, loc, pc, xcp)`
  note bisim2 = `P,i,n,h \<turnstile> (i, loc) \<leftrightarrow> ([], loc, 0, None)`
  note exec = `?exec (a\<lfloor>i\<rceil>) stk STK loc pc xcp stk' loc' pc' xcp'`
  from bisim1 have pc: "pc \<le> length (compE2 a)" by(rule bisim1_pc_length_compE2)
  show ?case
  proof(cases "pc < length (compE2 a)")
    case True
    with exec have "?exec a stk STK loc pc xcp stk' loc' pc' xcp'"
      by(simp add: compxE2_size_convs)(erule exec_meth_take_xt)
    from IH1[OF this] show ?thesis by auto
  next
    case False
    with pc have pc: "pc = length (compE2 a)" by simp
    with exec have "pc' \<ge> length (compE2 a)"
      by(simp add: compxE2_size_convs stack_xlift_compxE2)(auto elim!: exec_meth_drop_xt_pc)
    then obtain PC where PC: "pc' = PC + length (compE2 a)"
      by -(rule_tac PC="pc' - length (compE2 a)" in that, simp)
    from pc bisim1 obtain v where "stk = [v]" "xcp = None" by(auto dest: bisim1_pc_length_compE2D)
    with exec pc have "exec_meth (compP2 P) (compE2 a @ compE2 i)
   (stack_xlift (length STK) (compxE2 a 0 0 @ compxE2 i (length (compE2 a)) (Suc 0))) h (stk @ STK, loc, length (compE2 a) + 0, xcp) ta h' (stk', loc', pc', xcp')"
      by-(rule exec_meth_take, auto)
    hence "?exec i [] (v # STK) loc 0 None stk' loc' (pc' - length (compE2 a)) xcp'"
      using `stk = [v]` `xcp = None`
      by -(rule exec_meth_drop_xt, auto simp add: stack_xlift_compxE2 shift_compxE2)
    from IH2[OF this] PC obtain stk'' where stk': "stk' = stk'' @ v # STK"
      and "exec_meth (compP2 P) (compE2 i) (compxE2 i 0 0) h ([], loc, 0, None) ta h' (stk'', loc', PC, xcp')" by auto
    hence "exec_meth (compP2 P) ((compE2 a @ compE2 i) @ [ALoad])
        (compxE2 a 0 0 @ shift (length (compE2 a)) (stack_xlift (length [v]) (compxE2 i 0 0))) h
        ([] @ [v], loc, length (compE2 a) + 0, None) ta h' (stk'' @ [v], loc', length (compE2 a) + PC, xcp')"
      apply -
      apply(rule exec_meth_append)
      apply(rule append_exec_meth_xt)
      apply(erule exec_meth_stk_offer)
      by(auto)
    thus ?thesis using `stk = [v]` `xcp = None` stk' pc PC
      by(clarsimp simp add: shift_compxE2 stack_xlift_compxE2 add_ac)
  qed
next
  case (bisim1AAcc2 i n i' xs stk loc pc xcp a v1)
  note IH2 = `\<And>stk' loc' pc' xcp' STK. ?exec i stk STK loc pc xcp stk' loc' pc' xcp'
             \<Longrightarrow> ?concl i stk STK loc pc xcp stk' loc' pc' xcp'`
  note bisim2 = `P,i,n,h \<turnstile> (i', xs) \<leftrightarrow> (stk, loc, pc, xcp)`
  note exec = `?exec (a\<lfloor>i\<rceil>) (stk @ [v1]) STK loc (length (compE2 a) + pc) xcp stk' loc' pc' xcp'`
  from bisim2 have pc: "pc \<le> length (compE2 i)" by(rule bisim1_pc_length_compE2)
  show ?case
  proof(cases "pc < length (compE2 i)")
    case True
    from exec have "exec_meth (compP2 P) ((compE2 a @ compE2 i) @ [ALoad])
      (stack_xlift (length STK) (compxE2 a 0 0) @ shift (length (compE2 a)) (stack_xlift (length STK) (compxE2 i 0 (Suc 0))))
      h (stk @ v1 # STK, loc, length (compE2 a) + pc, xcp) ta h' (stk', loc', pc', xcp')" by(simp add: compxE2_size_convs)
    hence exec': "exec_meth (compP2 P) (compE2 a @ compE2 i) (stack_xlift (length STK) (compxE2 a 0 0) @
      shift (length (compE2 a)) (stack_xlift (length STK) (compxE2 i 0 (Suc 0))))
      h (stk @ v1 # STK, loc, length (compE2 a) + pc, xcp) ta h' (stk', loc', pc', xcp')"
      by(rule exec_meth_take)(simp add: True)
    hence "exec_meth (compP2 P) (compE2 i) (stack_xlift (length STK) (compxE2 i 0 (Suc 0)))
      h (stk @ v1 # STK, loc, pc, xcp) ta h' (stk', loc', pc' - length (compE2 a), xcp')"
      by(rule exec_meth_drop_xt)(auto simp add: stack_xlift_compxE2)
    hence "?exec i stk (v1 # STK) loc pc xcp stk' loc' (pc' - length (compE2 a)) xcp'"
      by(simp add: compxE2_stack_xlift_convs)
    from IH2[OF this] obtain stk'' where stk': "stk' = stk'' @ v1 # STK"
      and exec'': "exec_meth (compP2 P) (compE2 i) (compxE2 i 0 0) h (stk, loc, pc, xcp) ta h' (stk'', loc', pc' - length (compE2 a), xcp')" by blast
    from exec'' have "exec_meth (compP2 P) (compE2 i) (stack_xlift (length [v1]) (compxE2 i 0 0)) h (stk @ [v1], loc, pc, xcp)
      ta h' (stk'' @ [v1], loc', pc' - length (compE2 a), xcp')"
      by(rule exec_meth_stk_offer)
    hence "exec_meth (compP2 P) (compE2 a @ compE2 i) (compxE2 a 0 0 @ shift (length (compE2 a)) (stack_xlift (length [v1]) (compxE2 i 0 0))) h (stk @ [v1], loc, length (compE2 a) + pc, xcp)
      ta h' (stk'' @ [v1], loc', length (compE2 a) + (pc' - length (compE2 a)), xcp')"
      by(rule append_exec_meth_xt) auto
    hence "exec_meth (compP2 P) ((compE2 a @ compE2 i) @ [ALoad]) (compxE2 a 0 0 @ shift (length (compE2 a)) (stack_xlift (length [v1]) (compxE2 i 0 0))) h (stk @ [v1], loc, length (compE2 a) + pc, xcp)
      ta h' (stk'' @ [v1], loc', length (compE2 a) + (pc' - length (compE2 a)), xcp')"
      by(rule exec_meth_append)
    moreover from exec' have "pc' \<ge> length (compE2 a)"
      by(rule exec_meth_drop_xt_pc)(auto simp add: stack_xlift_compxE2)
    ultimately show ?thesis using stk' by(simp add: stack_xlift_compxE2 shift_compxE2)
  next
    case False
    with pc have pc: "pc = length (compE2 i)" by simp
    with bisim2 obtain v2 where [simp]: "stk = [v2]" "xcp = None"
      by(auto dest: dest: bisim1_pc_length_compE2D)
    with exec pc show ?thesis
      by(clarsimp)(erule exec_meth.cases, auto intro!: exec_meth.intros split: split_if_asm)
  qed
next
  case (bisim1AAccThrow1 A n a xs stk loc pc i)
  note bisim1 = `P,A,n,h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)`
  note IH1 = `\<And>stk' loc' pc' xcp' STK. ?exec A stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'
             \<Longrightarrow> ?concl A stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'`
  note exec = `?exec (A\<lfloor>i\<rceil>) stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'`
  from bisim1 have pc: "pc < length (compE2 A)" and [simp]: "xs = loc"
    by(auto dest: bisim1_ThrowD)
  from exec have "exec_meth (compP2 P) (compE2 A @ (compE2 i @ [ALoad]))
     (stack_xlift (length STK) (compxE2 A 0 0) @ shift (length (compE2 A)) (stack_xlift (length STK) (compxE2 i 0 (Suc 0))))
     h (stk @ STK, loc, pc, \<lfloor>a\<rfloor>) ta h' (stk', loc', pc', xcp')" by(simp add: compxE2_size_convs)
  hence "?exec A stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'" by(rule exec_meth_take_xt)(rule pc)
  from IH1[OF this] show ?case by(auto)
next
  case (bisim1AAccThrow2 i n a xs stk loc pc A v1)
  note bisim2 = `P,i,n,h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)`
  note IH2 = `\<And>stk' loc' pc' xcp' STK. ?exec i stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'
             \<Longrightarrow> ?concl i stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'`
  note exec = `?exec (A\<lfloor>i\<rceil>) (stk @ [v1]) STK loc (length (compE2 A) + pc) \<lfloor>a\<rfloor> stk' loc' pc' xcp'`
  from bisim2 have pc: "pc < length (compE2 i)" and [simp]: "xs = loc"
    by(auto dest: bisim1_ThrowD)
  from exec have "exec_meth (compP2 P) ((compE2 A @ compE2 i) @ [ALoad])
     (stack_xlift (length STK) (compxE2 A 0 0) @ shift (length (compE2 A)) (stack_xlift (length STK) (compxE2 i 0 (Suc 0))))
     h (stk @ v1 # STK, loc, length (compE2 A) + pc, \<lfloor>a\<rfloor>) ta h' (stk', loc', pc', xcp')"
    by(simp add: compxE2_size_convs)
  hence exec': "exec_meth (compP2 P) (compE2 A @ compE2 i)
     (stack_xlift (length STK) (compxE2 A 0 0) @ shift (length (compE2 A)) (stack_xlift (length STK) (compxE2 i 0 (Suc 0))))
     h (stk @ v1 # STK, loc, length (compE2 A) + pc, \<lfloor>a\<rfloor>) ta h' (stk', loc', pc', xcp')"
    by(rule exec_meth_take)(simp add: pc)
  hence "exec_meth (compP2 P) (compE2 i) (stack_xlift (length STK) (compxE2 i 0 (Suc 0)))
     h (stk @ v1 # STK, loc, pc, \<lfloor>a\<rfloor>) ta h' (stk', loc', pc' - length (compE2 A), xcp')"
    by(rule exec_meth_drop_xt)(auto simp add: stack_xlift_compxE2)
  hence "?exec i stk (v1 # STK) loc pc \<lfloor>a\<rfloor> stk' loc' (pc' - length (compE2 A)) xcp'"
    by(simp add: compxE2_stack_xlift_convs)
  from IH2[OF this] obtain stk'' where stk': "stk' = stk'' @ v1 # STK" and
    exec'': "exec_meth (compP2 P) (compE2 i) (compxE2 i 0 0) h (stk, loc, pc, \<lfloor>a\<rfloor>) ta h' (stk'', loc', pc' - length (compE2 A), xcp')" by blast
  from exec'' have "exec_meth (compP2 P) (compE2 i) (stack_xlift (length [v1]) (compxE2 i 0 0)) h (stk @ [v1], loc, pc, \<lfloor>a\<rfloor>)
      ta h' (stk'' @ [v1], loc', pc' - length (compE2 A), xcp')"
    by(rule exec_meth_stk_offer)
  hence "exec_meth (compP2 P) (compE2 A @ compE2 i) (compxE2 A 0 0 @ shift (length (compE2 A)) (stack_xlift (length [v1]) (compxE2 i 0 0))) h (stk @ [v1], loc, length (compE2 A) + pc, \<lfloor>a\<rfloor>)
      ta h' (stk'' @ [v1], loc', length (compE2 A) + (pc' - length (compE2 A)), xcp')"
    by(rule append_exec_meth_xt)(auto)
  hence "exec_meth (compP2 P) ((compE2 A @ compE2 i) @ [ALoad]) (compxE2 A 0 0 @ shift (length (compE2 A)) (stack_xlift (length [v1]) (compxE2 i 0 0))) h (stk @ [v1], loc, length (compE2 A) + pc, \<lfloor>a\<rfloor>)
      ta h' (stk'' @ [v1], loc', length (compE2 A) + (pc' - length (compE2 A)), xcp')"
    by(rule exec_meth_append)
  moreover from exec' have pc': "pc' \<ge> length (compE2 A)"
    by(rule exec_meth_drop_xt_pc)(auto simp add: stack_xlift_compxE2)
  ultimately show ?case using stk' by(auto simp add: stack_xlift_compxE2 shift_compxE2)
next
  case bisim1AAccNull thus ?case
    by(auto elim!: exec_meth.cases dest: match_ex_table_pcsD simp add: stack_xlift_compxEs2 stack_xlift_compxE2)
next
  case bisim1AAccBounds thus ?case
    by(auto elim!: exec_meth.cases dest: match_ex_table_pcsD simp add: stack_xlift_compxEs2 stack_xlift_compxE2)
next
  case (bisim1AAss1 a n a' xs stk loc pc xcp i e)
  note IH1 = `\<And>stk' loc' pc' xcp' STK. ?exec a stk STK loc pc xcp stk' loc' pc' xcp'
             \<Longrightarrow> ?concl a stk STK loc pc xcp stk' loc' pc' xcp'`
  note IH2 = `\<And>xs stk' loc' pc' xcp' STK. ?exec i [] STK xs 0 None stk' loc' pc' xcp'
             \<Longrightarrow> ?concl i [] STK xs 0 None stk' loc' pc' xcp'`
  note bisim1 = `P,a,n,h \<turnstile> (a', xs) \<leftrightarrow> (stk, loc, pc, xcp)`
  note bisim2 = `P,i,n,h \<turnstile> (i, loc) \<leftrightarrow> ([], loc, 0, None)`
  note exec = `?exec (a\<lfloor>i\<rceil> := e) stk STK loc pc xcp stk' loc' pc' xcp'`
  from bisim1 have pc: "pc \<le> length (compE2 a)" by(rule bisim1_pc_length_compE2)
  from exec have exec': "exec_meth (compP2 P) (compE2 a @ compE2 i @ compE2 e @ [AStore, Push Unit]) (stack_xlift (length STK) (compxE2 a 0 0) @ shift (length (compE2 a)) (stack_xlift (length STK) (compxE2 i 0 (Suc 0) @ compxE2 e (length (compE2 i)) (Suc (Suc 0))))) 
    h (stk @ STK, loc, pc, xcp) ta h' (stk', loc', pc', xcp')"
    by(simp add: compxE2_size_convs)
  show ?case
  proof(cases "pc < length (compE2 a)")
    case True
    with exec' have "?exec a stk STK loc pc xcp stk' loc' pc' xcp'" by(rule exec_meth_take_xt)
    from IH1[OF this] show ?thesis by auto
  next
    case False
    with pc have pc: "pc = length (compE2 a)" by simp
    with exec' have "pc' \<ge> length (compE2 a)" by -(erule exec_meth_drop_xt_pc, auto)
    then obtain PC where PC: "pc' = PC + length (compE2 a)"
      by -(rule_tac PC="pc' - length (compE2 a)" in that, simp)
    from pc bisim1 obtain v where "stk = [v]" "xcp = None" by(auto dest: bisim1_pc_length_compE2D)
    with exec PC pc
    have "exec_meth (compP2 P) ((compE2 a @ compE2 i) @ compE2 e @ [AStore, Push Unit]) (stack_xlift (length STK) (compxE2 a 0 0 @ shift (length (compE2 a)) (compxE2 i 0 (Suc 0))) @ shift (length (compE2 a @ compE2 i)) (compxE2 e 0 (length STK + Suc (Suc 0))))
    h (v # STK, loc, length (compE2 a) + 0, None) ta h' (stk', loc', length (compE2 a) + PC, xcp')" 
      by(simp add: shift_compxE2 stack_xlift_compxE2 add_ac)
    hence "exec_meth (compP2 P) (compE2 a @ compE2 i)
   (stack_xlift (length STK) (compxE2 a 0 0 @ shift (length (compE2 a)) (compxE2 i 0 (Suc 0)))) h (v # STK, loc, length (compE2 a) + 0, None) ta h' (stk', loc', length (compE2 a) + PC, xcp')"
      by(rule exec_meth_take_xt) simp
    hence "?exec i [] (v # STK) loc 0 None stk' loc' ((length (compE2 a) + PC) - length (compE2 a)) xcp'"
      by -(rule exec_meth_drop_xt, auto simp add: stack_xlift_compxE2 shift_compxE2)
    from IH2[OF this] PC obtain stk'' where stk': "stk' = stk'' @ v # STK"
      and "exec_meth (compP2 P) (compE2 i) (compxE2 i 0 0) h ([], loc, 0, None) ta h' (stk'', loc', PC, xcp')" by auto
    hence "exec_meth (compP2 P) ((compE2 a @ compE2 i) @ (compE2 e @ [AStore, Push Unit]))
        ((compxE2 a 0 0 @ shift (length (compE2 a)) (stack_xlift (length [v]) (compxE2 i 0 0))) @
         shift (length (compE2 a @ compE2 i)) (compxE2 e 0 (Suc (Suc 0)))) h
        ([] @ [v], loc, length (compE2 a) + 0, None) ta h' (stk'' @ [v], loc', length (compE2 a) + PC, xcp')"
      apply -
      apply(rule exec_meth_append_xt)
      apply(rule append_exec_meth_xt)
      apply(erule exec_meth_stk_offer)
      by(auto)
    thus ?thesis using `stk = [v]` `xcp = None` stk' pc PC
      by(clarsimp simp add: shift_compxE2 stack_xlift_compxE2 add_ac)
  qed
next
  case (bisim1AAss2 i n i' xs stk loc pc xcp a e v)
  note IH2 = `\<And>stk' loc' pc' xcp' STK. ?exec i stk STK loc pc xcp stk' loc' pc' xcp'
             \<Longrightarrow> ?concl i stk STK loc pc xcp stk' loc' pc' xcp'`
  note IH3 = `\<And>xs stk' loc' pc' xcp' STK. ?exec e [] STK xs 0 None stk' loc' pc' xcp'
             \<Longrightarrow> ?concl e [] STK xs 0 None stk' loc' pc' xcp'`
  note bisim2 = `P,i,n,h \<turnstile> (i', xs) \<leftrightarrow> (stk, loc, pc, xcp)`
  note bisim3 = `P,e,n,h \<turnstile> (e, loc) \<leftrightarrow> ([], loc, 0, None)`
  note exec = `?exec (a\<lfloor>i\<rceil> := e) (stk @ [v]) STK loc (length (compE2 a) + pc) xcp stk' loc' pc' xcp'`
  from bisim2 have pc: "pc \<le> length (compE2 i)" by(rule bisim1_pc_length_compE2)
  from exec have exec': "\<And>v'. exec_meth (compP2 P) ((compE2 a @ compE2 i) @ compE2 e @ [AStore, Push Unit]) ((compxE2 a 0 (length STK) @ shift (length (compE2 a)) (stack_xlift (length (v # STK)) (compxE2 i 0 0))) @ shift (length (compE2 a @ compE2 i)) (stack_xlift (length (v' # v # STK)) (compxE2 e 0 0)))
    h (stk @ v # STK, loc, length (compE2 a) + pc, xcp) ta h' (stk', loc', pc', xcp')"
    by(simp add: shift_compxE2 stack_xlift_compxE2)
  show ?case
  proof(cases "pc < length (compE2 i)")
    case True with exec'[of arbitrary]
    have exec'': "exec_meth (compP2 P) (compE2 a @ compE2 i) (compxE2 a 0 (length STK) @ shift (length (compE2 a)) (stack_xlift (length (v # STK)) (compxE2 i 0 0))) h (stk @ v # STK, loc, length (compE2 a) + pc, xcp) ta h' (stk', loc', pc', xcp')"
      by-(erule exec_meth_take_xt, simp)
    hence "?exec i stk (v # STK) loc pc xcp stk' loc' (pc' - length (compE2 a)) xcp'"
      by(rule exec_meth_drop_xt) auto
    from IH2[OF this] obtain stk'' where stk': "stk' = stk'' @ v # STK"
      and exec''': "exec_meth (compP2 P) (compE2 i) (compxE2 i 0 0) h (stk, loc, pc, xcp) ta h' (stk'', loc', pc' - length (compE2 a), xcp')" by blast
    from exec''' have "exec_meth (compP2 P) ((compE2 a @ compE2 i) @ compE2 e @ [AStore, Push Unit]) ((compxE2 a 0 0 @ shift (length (compE2 a)) (stack_xlift (length [v]) (compxE2 i 0 0))) @ shift (length (compE2 a @ compE2 i)) (compxE2 e 0 (Suc (Suc 0)))) h (stk @ [v], loc, length (compE2 a) + pc, xcp) ta h' (stk'' @ [v], loc', length (compE2 a) + (pc' - length (compE2 a)), xcp')"
      apply -
      apply(rule exec_meth_append_xt)
      apply(rule append_exec_meth_xt)
      apply(erule exec_meth_stk_offer)
      by auto
    moreover from exec'' have "pc' \<ge> length (compE2 a)"
      by(rule exec_meth_drop_xt_pc) auto
    ultimately show ?thesis using stk' by(auto simp add: shift_compxE2 stack_xlift_compxE2)
  next
    case False
    with pc have pc: "pc = length (compE2 i)" by simp
    with exec'[of arbitrary] have "pc' \<ge> length (compE2 a @ compE2 i)"
      by-(erule exec_meth_drop_xt_pc, auto simp add: shift_compxE2 stack_xlift_compxE2)
    then obtain PC where PC: "pc' = PC + length (compE2 a) + length (compE2 i)"
      by -(rule_tac PC="pc' - length (compE2 a @ compE2 i)" in that, simp)
    from pc bisim2 obtain v' where stk: "stk = [v']" and xcp: "xcp = None" by(auto dest: bisim1_pc_length_compE2D)
    from exec'[of v'] 
    have "exec_meth (compP2 P) (compE2 e @ [AStore, Push Unit]) (stack_xlift (length (v' # v # STK)) (compxE2 e 0 0))
                    h (v' # v # STK, loc, 0, xcp) ta h' (stk', loc', pc' - length (compE2 a @ compE2 i), xcp')"
      unfolding stk pc append_Cons append_Nil
      by -(rule exec_meth_drop_xt, simp only: add_0_right length_append, auto simp add: shift_compxE2 stack_xlift_compxE2)
    with PC xcp have "?exec e [] (v' # v # STK) loc 0 None stk' loc' PC xcp'"
      by -(rule exec_meth_take,auto)
    from IH3[OF this] obtain stk'' where stk': "stk' = stk'' @ v' # v # STK"
      and "exec_meth (compP2 P) (compE2 e) (compxE2 e 0 0) h ([], loc, 0, None) ta h' (stk'', loc', PC, xcp')"  by auto
    hence "exec_meth (compP2 P) (((compE2 a @ compE2 i) @ compE2 e) @ [AStore, Push Unit]) ((compxE2 a 0 0 @ compxE2 i (length (compE2 a)) (Suc 0)) @ shift (length (compE2 a @ compE2 i)) (stack_xlift (length [v', v]) (compxE2 e 0 0))) h ([] @ [v', v], loc, length (compE2 a @ compE2 i) + 0, None) ta h' (stk'' @ [v', v], loc', length (compE2 a @ compE2 i) + PC, xcp')"
      apply -
      apply(rule exec_meth_append)
      apply(rule append_exec_meth_xt)
      apply(erule exec_meth_stk_offer)
      by auto
    thus ?thesis using stk xcp stk' pc PC
      by(clarsimp simp add: shift_compxE2 stack_xlift_compxE2 add_ac)
  qed
next
  case (bisim1AAss3 e n e' xs stk loc pc xcp a i v1 v2)
  note IH3 = `\<And>stk' loc' pc' xcp' STK. ?exec e stk STK loc pc xcp stk' loc' pc' xcp'
             \<Longrightarrow> ?concl e stk STK loc pc xcp stk' loc' pc' xcp'`
  note bisim3 = `P,e,n,h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, xcp)`
  note exec = `?exec (a\<lfloor>i\<rceil> := e) (stk @ [v2, v1]) STK loc (length (compE2 a) + length (compE2 i) + pc) xcp stk' loc' pc' xcp'`
  from bisim3 have pc: "pc \<le> length (compE2 e)" by(rule bisim1_pc_length_compE2)
  show ?case
  proof(cases "pc < length (compE2 e)")
    case True
    from exec have "exec_meth (compP2 P) (((compE2 a @ compE2 i) @ compE2 e) @ [AStore, Push Unit])
      ((compxE2 a 0 (length STK) @ compxE2 i (length (compE2 a)) (Suc (length STK))) @ shift (length (compE2 a @ compE2 i)) (stack_xlift (length (v2 # v1 # STK)) (compxE2 e 0 0)))
      h (stk @ v2 # v1 # STK, loc, length (compE2 a @ compE2 i) + pc, xcp) ta h' (stk', loc', pc', xcp')"
      by(simp add: shift_compxE2 stack_xlift_compxE2)
    hence exec': "exec_meth (compP2 P) ((compE2 a @ compE2 i) @ compE2 e)
      ((compxE2 a 0 (length STK) @ compxE2 i (length (compE2 a)) (Suc (length STK))) @ shift (length (compE2 a @ compE2 i)) (stack_xlift (length (v2 # v1 # STK)) (compxE2 e 0 0)))
      h (stk @ v2 # v1 # STK, loc, length (compE2 a @ compE2 i) + pc, xcp) ta h' (stk', loc', pc', xcp')"
      by(rule exec_meth_take)(simp add: True)
    hence "?exec e stk (v2 # v1 # STK) loc pc xcp stk' loc' (pc' - length (compE2 a @ compE2 i)) xcp'"
      by(rule exec_meth_drop_xt) auto
    from IH3[OF this] obtain stk'' where stk': "stk' = stk'' @ v2 # v1 # STK"
      and exec'': "exec_meth (compP2 P) (compE2 e) (compxE2 e 0 0) h (stk, loc, pc, xcp) ta h' (stk'', loc', pc' - length (compE2 a @ compE2 i), xcp')" by blast
    from exec'' have "exec_meth (compP2 P) (compE2 e) (stack_xlift (length [v2, v1]) (compxE2 e 0 0)) h (stk @ [v2, v1], loc, pc, xcp)
      ta h' (stk'' @ [v2, v1], loc', pc' - length (compE2 a @ compE2 i), xcp')"
      by(rule exec_meth_stk_offer)
    hence "exec_meth (compP2 P) ((compE2 a @ compE2 i) @ compE2 e) ((compxE2 a 0 0 @ compxE2 i (length (compE2 a)) (Suc 0)) @ shift (length (compE2 a @ compE2 i)) (stack_xlift (length [v2, v1]) (compxE2 e 0 0))) h (stk @ [v2, v1], loc, length (compE2 a @ compE2 i) + pc, xcp)
      ta h' (stk'' @ [v2, v1], loc', length (compE2 a @ compE2 i) + (pc' - length (compE2 a @ compE2 i)), xcp')"
      by(rule append_exec_meth_xt) auto
    hence "exec_meth (compP2 P) (((compE2 a @ compE2 i) @ compE2 e) @ [AStore, Push Unit]) ((compxE2 a 0 0 @ compxE2 i (length (compE2 a)) (Suc 0)) @ shift (length (compE2 a @ compE2 i)) (stack_xlift (length [v2, v1]) (compxE2 e 0 0))) h (stk @ [v2, v1], loc, length (compE2 a @ compE2 i) + pc, xcp)
      ta h' (stk'' @ [v2, v1], loc', length (compE2 a @ compE2 i) + (pc' - length (compE2 a @ compE2 i)), xcp')"
      by(rule exec_meth_append)
    moreover from exec' have "pc' \<ge> length (compE2 a @ compE2 i)"
      by(rule exec_meth_drop_xt_pc)(auto simp add: stack_xlift_compxE2)
    ultimately show ?thesis using stk' by(simp add: stack_xlift_compxE2 shift_compxE2)
  next
    case False
    with pc have pc: "pc = length (compE2 e)" by simp
    with bisim3 obtain v3 where [simp]: "stk = [v3]" "xcp = None"
      by(auto dest: dest: bisim1_pc_length_compE2D)
    with exec pc show ?thesis apply(simp)
      by(erule exec_meth.cases)(auto intro!: exec_meth.intros split: split_if_asm)
  qed
next
  case (bisim1AAssThrow1 A n a xs stk loc pc i e)
  note bisim1 = `P,A,n,h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)`
  note IH1 = `\<And>stk' loc' pc' xcp' STK. ?exec A stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'
             \<Longrightarrow> ?concl A stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'`
  note exec = `?exec (A\<lfloor>i\<rceil> := e) stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'`
  from bisim1 have pc: "pc < length (compE2 A)" and [simp]: "xs = loc"
    by(auto dest: bisim1_ThrowD)
  from exec have "exec_meth (compP2 P) (compE2 A @ (compE2 i @ compE2 e @ [AStore, Push Unit]))
     (stack_xlift (length STK) (compxE2 A 0 0) @ shift (length (compE2 A)) (stack_xlift (length STK) (compxE2 i 0 (Suc 0) @ compxE2 e (length (compE2 i)) (Suc (Suc 0)))))
     h (stk @ STK, loc, pc, \<lfloor>a\<rfloor>) ta h' (stk', loc', pc', xcp')" by(simp add: compxE2_size_convs)
  hence "?exec A stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'" by(rule exec_meth_take_xt)(rule pc)
  from IH1[OF this] show ?case by(auto)
next
  case (bisim1AAssThrow2 i n a xs stk loc pc A e v1)
  note bisim2 = `P,i,n,h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)`
  note IH2 = `\<And>stk' loc' pc' xcp' STK. ?exec i stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'
             \<Longrightarrow> ?concl i stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'`
  note exec = `?exec (A\<lfloor>i\<rceil> := e) (stk @ [v1]) STK loc (length (compE2 A) + pc) \<lfloor>a\<rfloor> stk' loc' pc' xcp'`
  from bisim2 have pc: "pc < length (compE2 i)" and [simp]: "xs = loc"
    by(auto dest: bisim1_ThrowD)
  from exec have "exec_meth (compP2 P) ((compE2 A @ compE2 i) @ compE2 e @ [AStore, Push Unit])
     ((stack_xlift (length STK) (compxE2 A 0 0) @ shift (length (compE2 A)) (stack_xlift (length STK) (compxE2 i 0 (Suc 0)))) @ (shift (length (compE2 A @ compE2 i)) (compxE2 e 0 (Suc (Suc (length STK))))))
     h (stk @ v1 # STK, loc, length (compE2 A) + pc, \<lfloor>a\<rfloor>) ta h' (stk', loc', pc', xcp')"
    by(simp add: shift_compxE2 stack_xlift_compxE2 add_ac)
  hence exec': "exec_meth (compP2 P) (compE2 A @ compE2 i)
     (stack_xlift (length STK) (compxE2 A 0 0) @ shift (length (compE2 A)) (stack_xlift (length STK) (compxE2 i 0 (Suc 0))))
     h (stk @ v1 # STK, loc, length (compE2 A) + pc, \<lfloor>a\<rfloor>) ta h' (stk', loc', pc', xcp')"
    by(rule exec_meth_take_xt)(simp add: pc)
  hence "exec_meth (compP2 P) (compE2 i) (stack_xlift (length STK) (compxE2 i 0 (Suc 0)))
     h (stk @ v1 # STK, loc, pc, \<lfloor>a\<rfloor>) ta h' (stk', loc', pc' - length (compE2 A), xcp')"
    by(rule exec_meth_drop_xt)(auto simp add: stack_xlift_compxE2)
  hence "?exec i stk (v1 # STK) loc pc \<lfloor>a\<rfloor> stk' loc' (pc' - length (compE2 A)) xcp'"
    by(simp add: compxE2_stack_xlift_convs)
  from IH2[OF this] obtain stk'' where stk': "stk' = stk'' @ v1 # STK" and
    exec'': "exec_meth (compP2 P) (compE2 i) (compxE2 i 0 0) h (stk, loc, pc, \<lfloor>a\<rfloor>) ta h' (stk'', loc', pc' - length (compE2 A), xcp')" by blast
  from exec'' have "exec_meth (compP2 P) (compE2 i) (stack_xlift (length [v1]) (compxE2 i 0 0)) h (stk @ [v1], loc, pc, \<lfloor>a\<rfloor>)
      ta h' (stk'' @ [v1], loc', pc' - length (compE2 A), xcp')"
    by(rule exec_meth_stk_offer)
  hence "exec_meth (compP2 P) (compE2 A @ compE2 i) (compxE2 A 0 0 @ shift (length (compE2 A)) (stack_xlift (length [v1]) (compxE2 i 0 0))) h (stk @ [v1], loc, length (compE2 A) + pc, \<lfloor>a\<rfloor>)
      ta h' (stk'' @ [v1], loc', length (compE2 A) + (pc' - length (compE2 A)), xcp')"
    by(rule append_exec_meth_xt)(auto)
  hence "exec_meth (compP2 P) ((compE2 A @ compE2 i) @ compE2 e @ [AStore, Push Unit]) ((compxE2 A 0 0 @ shift (length (compE2 A)) (stack_xlift (length [v1]) (compxE2 i 0 0))) @ (shift (length (compE2 A @ compE2 i)) (compxE2 e 0 (Suc (Suc 0))))) h (stk @ [v1], loc, length (compE2 A) + pc, \<lfloor>a\<rfloor>)
      ta h' (stk'' @ [v1], loc', length (compE2 A) + (pc' - length (compE2 A)), xcp')"
    by(rule exec_meth_append_xt)
  moreover from exec' have pc': "pc' \<ge> length (compE2 A)"
    by(rule exec_meth_drop_xt_pc)(auto simp add: stack_xlift_compxE2)
  ultimately show ?case using stk' by(auto simp add: stack_xlift_compxE2 shift_compxE2)
next
  case (bisim1AAssThrow3 e n a xs stk loc pc A i v2 v1)
  note bisim3 = `P,e,n,h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)`
  note IH3 = `\<And>stk' loc' pc' xcp' STK. ?exec e stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'
             \<Longrightarrow> ?concl e stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'`
  note exec = `?exec (A\<lfloor>i\<rceil> := e) (stk @ [v2, v1]) STK loc (length (compE2 A) + length (compE2 i) + pc) \<lfloor>a\<rfloor> stk' loc' pc' xcp'`
  from bisim3 have pc: "pc < length (compE2 e)" and [simp]: "xs = loc"
    by(auto dest: bisim1_ThrowD)
  from exec have "exec_meth (compP2 P) (((compE2 A @ compE2 i) @ compE2 e) @ [AStore, Push Unit])
     ((stack_xlift (length STK) (compxE2 A 0 0 @ compxE2 i (length (compE2 A)) (Suc 0))) @ shift (length (compE2 A @ compE2 i)) (stack_xlift (length (v2 # v1 # STK)) (compxE2 e 0 0)))
     h (stk @ v2 # v1 # STK, loc, length (compE2 A @ compE2 i) + pc, \<lfloor>a\<rfloor>) ta h' (stk', loc', pc', xcp')"
    by(simp add: shift_compxE2 stack_xlift_compxE2 add_ac)
  hence exec': "exec_meth (compP2 P) ((compE2 A @ compE2 i) @ compE2 e)
     ((stack_xlift (length STK) (compxE2 A 0 0 @ compxE2 i (length (compE2 A)) (Suc 0))) @ shift (length (compE2 A @ compE2 i)) (stack_xlift (length (v2 # v1 # STK)) (compxE2 e 0 0)))
     h (stk @ v2 # v1 # STK, loc, length (compE2 A @ compE2 i) + pc, \<lfloor>a\<rfloor>) ta h' (stk', loc', pc', xcp')"
    by(rule exec_meth_take)(simp add: pc)
  hence "?exec e stk (v2 # v1 # STK) loc pc \<lfloor>a\<rfloor> stk' loc' (pc' - length (compE2 A @ compE2 i)) xcp'"
    by(rule exec_meth_drop_xt) auto
  from IH3[OF this] obtain stk'' where stk': "stk' = stk'' @ v2 # v1 # STK" and
    exec'': "exec_meth (compP2 P) (compE2 e) (compxE2 e 0 0) h (stk, loc, pc, \<lfloor>a\<rfloor>) ta h' (stk'', loc', pc' - length (compE2 A @ compE2 i), xcp')" by blast
  from exec'' have "exec_meth (compP2 P) (compE2 e) (stack_xlift (length [v2, v1]) (compxE2 e 0 0)) h (stk @ [v2, v1], loc, pc, \<lfloor>a\<rfloor>)
      ta h' (stk'' @ [v2, v1], loc', pc' - length (compE2 A @ compE2 i), xcp')"
    by(rule exec_meth_stk_offer)
  hence "exec_meth (compP2 P) ((compE2 A @ compE2 i) @ compE2 e) ((compxE2 A 0 0 @ compxE2 i (length (compE2 A)) (Suc 0)) @ shift (length (compE2 A @ compE2 i)) (stack_xlift (length [v2, v1]) (compxE2 e 0 0))) h (stk @ [v2, v1], loc, length (compE2 A @ compE2 i) + pc, \<lfloor>a\<rfloor>)
      ta h' (stk'' @ [v2, v1], loc', length (compE2 A @ compE2 i) + (pc' - length (compE2 A @ compE2 i)), xcp')"
    by(rule append_exec_meth_xt)(auto)
  hence "exec_meth (compP2 P) (((compE2 A @ compE2 i) @ compE2 e) @ [AStore, Push Unit]) ((compxE2 A 0 0 @ compxE2 i (length (compE2 A)) (Suc 0)) @ shift (length (compE2 A @ compE2 i)) (stack_xlift (length [v2, v1]) (compxE2 e 0 0))) h (stk @ [v2, v1], loc, length (compE2 A @ compE2 i) + pc, \<lfloor>a\<rfloor>)
      ta h' (stk'' @ [v2, v1], loc', length (compE2 A @ compE2 i) + (pc' - length (compE2 A @ compE2 i)), xcp')"
    by(rule exec_meth_append)
  moreover from exec' have pc': "pc' \<ge> length (compE2 A @ compE2 i)"
    by(rule exec_meth_drop_xt_pc)(auto simp add: stack_xlift_compxE2)
  ultimately show ?case using stk' by(auto simp add: stack_xlift_compxE2 shift_compxE2)
next
  case bisim1AAssNull thus ?case
    by(auto elim!: exec_meth.cases dest: match_ex_table_pcsD simp add: stack_xlift_compxEs2 stack_xlift_compxE2)
next
  case bisim1AAssBounds thus ?case
    by(auto elim!: exec_meth.cases dest: match_ex_table_pcsD simp add: stack_xlift_compxEs2 stack_xlift_compxE2)
next
  case bisim1AAssStore thus ?case
    by(auto elim!: exec_meth.cases dest: match_ex_table_pcsD simp add: stack_xlift_compxEs2 stack_xlift_compxE2)
next
  case bisim1AAss4 thus ?case
    by -(erule exec_meth.cases, auto intro!: exec_meth.exec_instr)
next
  case (bisim1ALength a n a' xs stk loc pc xcp)
  note bisim = `P,a,n,h \<turnstile> (a', xs) \<leftrightarrow> (stk, loc, pc, xcp)`
  note IH = `\<And>stk' loc' pc' xcp' STK. ?exec a stk STK loc pc xcp stk' loc' pc' xcp'
             \<Longrightarrow> ?concl a stk STK loc pc xcp stk' loc' pc' xcp'`
  note exec = `?exec (a\<bullet>length) stk STK loc pc xcp stk' loc' pc' xcp'`
  from bisim have pc: "pc \<le> length (compE2 a)" by(rule bisim1_pc_length_compE2)
  show ?case
  proof(cases "pc < length (compE2 a)")
    case True
    with exec have "?exec a stk STK loc pc xcp stk' loc' pc' xcp'"
      by(simp add: compxE2_size_convs)(erule exec_meth_take)
    from IH[OF this] show ?thesis by auto
  next
    case False
    with pc have [simp]: "pc = length (compE2 a)" by simp
    with bisim obtain v where [simp]: "stk = [v]" "xcp = None"
      by(auto dest: dest: bisim1_pc_length_compE2D)
    with exec show ?thesis apply(simp)
      by(erule exec_meth.cases)(auto intro!: exec_meth.intros split: split_if_asm)
  qed
next
  case (bisim1ALengthThrow e n a xs stk loc pc)
  note bisim = `P,e,n,h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)`
  note IH = `\<And>stk' loc' pc' xcp' STK. ?exec e stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'
             \<Longrightarrow> ?concl e stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'`
  note exec = `?exec (e\<bullet>length) stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'`
  from bisim have pc: "pc < length (compE2 e)" and [simp]: "xs = loc"
    by(auto dest: bisim1_ThrowD)
  from exec have "?exec e stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'"
    by(simp)(erule exec_meth_take[OF _ pc])
  from IH[OF this] show ?case by(auto)
next
  case bisim1ALengthNull thus ?case
    by(auto elim!: exec_meth.cases dest: match_ex_table_pcsD simp add: stack_xlift_compxEs2 stack_xlift_compxE2)
next
  case (bisim1FAcc e n e' xs stk loc pc xcp F D)
  note bisim = `P,e,n,h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, xcp)`
  note IH = `\<And>stk' loc' pc' xcp' STK. ?exec e stk STK loc pc xcp stk' loc' pc' xcp'
             \<Longrightarrow> ?concl e stk STK loc pc xcp stk' loc' pc' xcp'`
  note exec = `?exec (e\<bullet>F{D}) stk STK loc pc xcp stk' loc' pc' xcp'`
  from bisim have pc: "pc \<le> length (compE2 e)" by(rule bisim1_pc_length_compE2)
  show ?case
  proof(cases "pc < length (compE2 e)")
    case True
    with exec have "?exec e stk STK loc pc xcp stk' loc' pc' xcp'"
      by(simp add: compxE2_size_convs)(erule exec_meth_take)
    from IH[OF this] show ?thesis by auto
  next
    case False
    with pc have [simp]: "pc = length (compE2 e)" by simp
    with bisim obtain v where [simp]: "stk = [v]" "xcp = None"
      by(auto dest: dest: bisim1_pc_length_compE2D)
    with exec show ?thesis apply(simp)
      by(erule exec_meth.cases)(fastsimp elim!: is_ArrE intro!: exec_meth.intros simp add: is_Ref_def split: split_if_asm)+
  qed
next
  case (bisim1FAccThrow e n a xs stk loc pc F D)
  note bisim = `P,e,n,h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)`
  note IH = `\<And>stk' loc' pc' xcp' STK. ?exec e stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'
             \<Longrightarrow> ?concl e stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'`
  note exec = `?exec (e\<bullet>F{D}) stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'`
  from bisim have pc: "pc < length (compE2 e)" and [simp]: "xs = loc"
    by(auto dest: bisim1_ThrowD)
  from exec have "?exec e stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'"
    by(simp)(erule exec_meth_take[OF _ pc])
  from IH[OF this] show ?case by(auto)
next
  case bisim1FAccNull thus ?case
    by(auto elim!: exec_meth.cases dest: match_ex_table_pcsD simp add: stack_xlift_compxEs2 stack_xlift_compxE2)
next
  case (bisim1FAss1 e n e' xs stk loc pc xcp e2 F D)
  note IH1 = `\<And>stk' loc' pc' xcp' STK. ?exec e stk STK loc pc xcp stk' loc' pc' xcp'
             \<Longrightarrow> ?concl e stk STK loc pc xcp stk' loc' pc' xcp'`
  note IH2 = `\<And>xs stk' loc' pc' xcp' STK. ?exec e2 [] STK xs 0 None stk' loc' pc' xcp'
             \<Longrightarrow> ?concl e2 [] STK xs 0 None stk' loc' pc' xcp'`
  note bisim1 = `P,e,n,h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, xcp)`
  note bisim2 = `P,e2,n,h \<turnstile> (e2, loc) \<leftrightarrow> ([], loc, 0, None)`
  note exec = `?exec (e\<bullet>F{D} := e2) stk STK loc pc xcp stk' loc' pc' xcp'`
  from bisim1 have pc: "pc \<le> length (compE2 e)" by(rule bisim1_pc_length_compE2)
  show ?case
  proof(cases "pc < length (compE2 e)")
    case True
    with exec have "?exec e stk STK loc pc xcp stk' loc' pc' xcp'"
      by(simp add: compxE2_size_convs)(erule exec_meth_take_xt)
    from IH1[OF this] show ?thesis by auto
  next
    case False
    with pc have pc: "pc = length (compE2 e)" by simp
    with exec have "pc' \<ge> length (compE2 e)"
      by(simp add: compxE2_size_convs stack_xlift_compxE2)(auto elim!: exec_meth_drop_xt_pc)
    then obtain PC where PC: "pc' = PC + length (compE2 e)"
      by -(rule_tac PC="pc' - length (compE2 e)" in that, simp)
    from pc bisim1 obtain v where "stk = [v]" "xcp = None" by(auto dest: bisim1_pc_length_compE2D)
    with exec pc have "exec_meth (compP2 P) (compE2 e @ compE2 e2)
   (stack_xlift (length STK) (compxE2 e 0 0 @ compxE2 e2 (length (compE2 e)) (Suc 0))) h (stk @ STK, loc, length (compE2 e) + 0, xcp) ta h' (stk', loc', pc', xcp')"
      by-(rule exec_meth_take, auto)
    hence "?exec e2 [] (v # STK) loc 0 None stk' loc' (pc' - length (compE2 e)) xcp'"
      using `stk = [v]` `xcp = None`
      by -(rule exec_meth_drop_xt, auto simp add: stack_xlift_compxE2 shift_compxE2)
    from IH2[OF this] PC obtain stk'' where stk': "stk' = stk'' @ v # STK"
      and "exec_meth (compP2 P) (compE2 e2) (compxE2 e2 0 0) h ([], loc, 0, None) ta h' (stk'', loc', PC, xcp')" by auto
    hence "exec_meth (compP2 P) ((compE2 e @ compE2 e2) @ [Putfield F D, Push Unit])
        (compxE2 e 0 0 @ shift (length (compE2 e)) (stack_xlift (length [v]) (compxE2 e2 0 0))) h
        ([] @ [v], loc, length (compE2 e) + 0, None) ta h' (stk'' @ [v], loc', length (compE2 e) + PC, xcp')"
      apply -
      apply(rule exec_meth_append)
      apply(rule append_exec_meth_xt)
      apply(erule exec_meth_stk_offer)
      by(auto)
    thus ?thesis using `stk = [v]` `xcp = None` stk' pc PC
      by(clarsimp simp add: shift_compxE2 stack_xlift_compxE2 add_ac)
  qed
next
  case (bisim1FAss2 e2 n e' xs stk loc pc xcp e F D v1)
  note IH2 = `\<And>stk' loc' pc' xcp' STK. ?exec e2 stk STK loc pc xcp stk' loc' pc' xcp'
             \<Longrightarrow> ?concl e2 stk STK loc pc xcp stk' loc' pc' xcp'`
  note bisim2 = `P,e2,n,h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, xcp)`
  note exec = `?exec (e\<bullet>F{D} := e2) (stk @ [v1]) STK loc (length (compE2 e) + pc) xcp stk' loc' pc' xcp'`
  from bisim2 have pc: "pc \<le> length (compE2 e2)" by(rule bisim1_pc_length_compE2)
  show ?case
  proof(cases "pc < length (compE2 e2)")
    case True
    from exec have "exec_meth (compP2 P) ((compE2 e @ compE2 e2) @ [Putfield F D, Push Unit])
      (stack_xlift (length STK) (compxE2 e 0 0) @ shift (length (compE2 e)) (stack_xlift (length STK) (compxE2 e2 0 (Suc 0))))
      h (stk @ v1 # STK, loc, length (compE2 e) + pc, xcp) ta h' (stk', loc', pc', xcp')" by(simp add: compxE2_size_convs)
    hence exec': "exec_meth (compP2 P) (compE2 e @ compE2 e2) (stack_xlift (length STK) (compxE2 e 0 0) @
      shift (length (compE2 e)) (stack_xlift (length STK) (compxE2 e2 0 (Suc 0))))
      h (stk @ v1 # STK, loc, length (compE2 e) + pc, xcp) ta h' (stk', loc', pc', xcp')"
      by(rule exec_meth_take)(simp add: True)
    hence "exec_meth (compP2 P) (compE2 e2) (stack_xlift (length STK) (compxE2 e2 0 (Suc 0)))
      h (stk @ v1 # STK, loc, pc, xcp) ta h' (stk', loc', pc' - length (compE2 e), xcp')"
      by(rule exec_meth_drop_xt)(auto simp add: stack_xlift_compxE2)
    hence "?exec e2 stk (v1 # STK) loc pc xcp stk' loc' (pc' - length (compE2 e)) xcp'"
      by(simp add: compxE2_stack_xlift_convs)
    from IH2[OF this] obtain stk'' where stk': "stk' = stk'' @ v1 # STK"
      and exec'': "exec_meth (compP2 P) (compE2 e2) (compxE2 e2 0 0) h (stk, loc, pc, xcp) ta h' (stk'', loc', pc' - length (compE2 e), xcp')" by blast
    from exec'' have "exec_meth (compP2 P) (compE2 e2) (stack_xlift (length [v1]) (compxE2 e2 0 0)) h (stk @ [v1], loc, pc, xcp)
      ta h' (stk'' @ [v1], loc', pc' - length (compE2 e), xcp')"
      by(rule exec_meth_stk_offer)
    hence "exec_meth (compP2 P) (compE2 e @ compE2 e2) (compxE2 e 0 0 @ shift (length (compE2 e)) (stack_xlift (length [v1]) (compxE2 e2 0 0))) h (stk @ [v1], loc, length (compE2 e) + pc, xcp)
      ta h' (stk'' @ [v1], loc', length (compE2 e) + (pc' - length (compE2 e)), xcp')"
      by(rule append_exec_meth_xt) auto
    hence "exec_meth (compP2 P) ((compE2 e @ compE2 e2) @ [Putfield F D, Push Unit]) (compxE2 e 0 0 @ shift (length (compE2 e)) (stack_xlift (length [v1]) (compxE2 e2 0 0))) h (stk @ [v1], loc, length (compE2 e) + pc, xcp)
      ta h' (stk'' @ [v1], loc', length (compE2 e) + (pc' - length (compE2 e)), xcp')"
      by(rule exec_meth_append)
    moreover from exec' have "pc' \<ge> length (compE2 e)"
      by(rule exec_meth_drop_xt_pc)(auto simp add: stack_xlift_compxE2)
    ultimately show ?thesis using stk' by(simp add: stack_xlift_compxE2 shift_compxE2)
  next
    case False
    with pc have pc: "pc = length (compE2 e2)" by simp
    with bisim2 obtain v2 where [simp]: "stk = [v2]" "xcp = None"
      by(auto dest: dest: bisim1_pc_length_compE2D)
    with exec pc show ?thesis apply(simp)
      by(erule exec_meth.cases)(fastsimp intro!: exec_meth.intros split: split_if_asm)+
  qed
next
  case (bisim1FAssThrow1 e n a xs stk loc pc e2 F D)
  note bisim1 = `P,e,n,h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)`
  note IH1 = `\<And>stk' loc' pc' xcp' STK. ?exec e stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'
             \<Longrightarrow> ?concl e stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'`
  note exec = `?exec (e\<bullet>F{D} := e2) stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'`
  from bisim1 have pc: "pc < length (compE2 e)" and [simp]: "xs = loc"
    by(auto dest: bisim1_ThrowD)
  from exec have "exec_meth (compP2 P) (compE2 e @ (compE2 e2 @ [Putfield F D, Push Unit]))
     (stack_xlift (length STK) (compxE2 e 0 0) @ shift (length (compE2 e)) (stack_xlift (length STK) (compxE2 e2 0 (Suc 0))))
     h (stk @ STK, loc, pc, \<lfloor>a\<rfloor>) ta h' (stk', loc', pc', xcp')" by(simp add: compxE2_size_convs)
  hence "?exec e stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'" by(rule exec_meth_take_xt)(rule pc)
  from IH1[OF this] show ?case by(auto)
next
  case (bisim1FAssThrow2 e2 n a xs stk loc pc e F D v1)
  note bisim2 = `P,e2,n,h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)`
  note IH2 = `\<And>stk' loc' pc' xcp' STK. ?exec e2 stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'
             \<Longrightarrow> ?concl e2 stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'`
  note exec = `?exec (e\<bullet>F{D} := e2) (stk @ [v1]) STK loc (length (compE2 e) + pc) \<lfloor>a\<rfloor> stk' loc' pc' xcp'`
  from bisim2 have pc: "pc < length (compE2 e2)" and [simp]: "xs = loc"
    by(auto dest: bisim1_ThrowD)
  from exec have "exec_meth (compP2 P) ((compE2 e @ compE2 e2) @ [Putfield F D, Push Unit])
     (stack_xlift (length STK) (compxE2 e 0 0) @ shift (length (compE2 e)) (stack_xlift (length STK) (compxE2 e2 0 (Suc 0))))
     h (stk @ v1 # STK, loc, length (compE2 e) + pc, \<lfloor>a\<rfloor>) ta h' (stk', loc', pc', xcp')"
    by(simp add: compxE2_size_convs)
  hence exec': "exec_meth (compP2 P) (compE2 e @ compE2 e2)
     (stack_xlift (length STK) (compxE2 e 0 0) @ shift (length (compE2 e)) (stack_xlift (length STK) (compxE2 e2 0 (Suc 0))))
     h (stk @ v1 # STK, loc, length (compE2 e) + pc, \<lfloor>a\<rfloor>) ta h' (stk', loc', pc', xcp')"
    by(rule exec_meth_take)(simp add: pc)
  hence "exec_meth (compP2 P) (compE2 e2) (stack_xlift (length STK) (compxE2 e2 0 (Suc 0)))
     h (stk @ v1 # STK, loc, pc, \<lfloor>a\<rfloor>) ta h' (stk', loc', pc' - length (compE2 e), xcp')"
    by(rule exec_meth_drop_xt)(auto simp add: stack_xlift_compxE2)
  hence "?exec e2 stk (v1 # STK) loc pc \<lfloor>a\<rfloor> stk' loc' (pc' - length (compE2 e)) xcp'"
    by(simp add: compxE2_stack_xlift_convs)
  from IH2[OF this] obtain stk'' where stk': "stk' = stk'' @ v1 # STK" and
    exec'': "exec_meth (compP2 P) (compE2 e2) (compxE2 e2 0 0) h (stk, loc, pc, \<lfloor>a\<rfloor>) ta h' (stk'', loc', pc' - length (compE2 e), xcp')" by blast
  from exec'' have "exec_meth (compP2 P) (compE2 e2) (stack_xlift (length [v1]) (compxE2 e2 0 0)) h (stk @ [v1], loc, pc, \<lfloor>a\<rfloor>)
      ta h' (stk'' @ [v1], loc', pc' - length (compE2 e), xcp')"
    by(rule exec_meth_stk_offer)
  hence "exec_meth (compP2 P) (compE2 e @ compE2 e2) (compxE2 e 0 0 @ shift (length (compE2 e)) (stack_xlift (length [v1]) (compxE2 e2 0 0))) h (stk @ [v1], loc, length (compE2 e) + pc, \<lfloor>a\<rfloor>)
      ta h' (stk'' @ [v1], loc', length (compE2 e) + (pc' - length (compE2 e)), xcp')"
    by(rule append_exec_meth_xt)(auto)
  hence "exec_meth (compP2 P) ((compE2 e @ compE2 e2) @ [Putfield F D, Push Unit]) (compxE2 e 0 0 @ shift (length (compE2 e)) (stack_xlift (length [v1]) (compxE2 e2 0 0))) h (stk @ [v1], loc, length (compE2 e) + pc, \<lfloor>a\<rfloor>)
      ta h' (stk'' @ [v1], loc', length (compE2 e) + (pc' - length (compE2 e)), xcp')"
    by(rule exec_meth_append)
  moreover from exec' have pc': "pc' \<ge> length (compE2 e)"
    by(rule exec_meth_drop_xt_pc)(auto simp add: stack_xlift_compxE2)
  ultimately show ?case using stk' by(auto simp add: stack_xlift_compxE2 shift_compxE2)
next
  case bisim1FAssNull thus ?case
    by(auto elim!: exec_meth.cases dest: match_ex_table_pcsD simp add: stack_xlift_compxEs2 stack_xlift_compxE2)
next
  case bisim1FAss3 thus ?case
    by -(erule exec_meth.cases, auto intro!: exec_meth.exec_instr)
next
  case (bisim1Call1 obj n obj' xs stk loc pc xcp ps M')
  note bisimObj = `P,obj,n,h \<turnstile> (obj', xs) \<leftrightarrow> (stk, loc, pc, xcp)`
  note IHobj = `\<And>stk' loc' pc' xcp' STK. ?exec obj stk STK loc pc xcp stk' loc' pc' xcp'
             \<Longrightarrow> ?concl obj stk STK loc pc xcp stk' loc' pc' xcp'`
  note IHparams = `\<And>xs stk' loc' pc' xcp' STK. ?execs ps [] STK xs 0 None stk' loc' pc' xcp'
             \<Longrightarrow> ?concls ps [] STK xs 0 None stk' loc' pc' xcp'`
  note exec = `?exec (obj\<bullet>M'(ps)) stk STK loc pc xcp stk' loc' pc' xcp'`
  from bisimObj have pc: "pc \<le> length (compE2 obj)" by(rule bisim1_pc_length_compE2)
  show ?case
  proof(cases "pc < length (compE2 obj)")
    case True
    from exec have "?exec obj stk STK loc pc xcp stk' loc' pc' xcp'"
      by(simp add: compxEs2_size_convs)(erule exec_meth_take_xt[OF _ True])
    from IHobj[OF this] show ?thesis by auto
  next
    case False
    with pc have [simp]: "pc = length (compE2 obj)" by simp
    with exec have "pc' \<ge> length (compE2 obj)"
      by(simp add: compxEs2_size_convs stack_xlift_compxE2)(auto elim!: exec_meth_drop_xt_pc)
    then obtain PC where PC: "pc' = PC + length (compE2 obj)"
      by -(rule_tac PC="pc' - length (compE2 obj)" in that, simp)
    from pc bisimObj obtain v where [simp]: "stk = [v]" "xcp = None" by(auto dest: bisim1_pc_length_compE2D)
    show ?thesis
    proof(cases ps)
      case Cons
      with exec pc have "exec_meth (compP2 P) (compE2 obj @ compEs2 ps)
	(stack_xlift (length STK) (compxE2 obj 0 0 @ compxEs2 ps (length (compE2 obj)) (Suc 0))) h (stk @ STK, loc, length (compE2 obj) + 0, xcp) ta h' (stk', loc', pc', xcp')"
	by -(rule exec_meth_take, auto)
      hence "?execs ps [] (v # STK) loc 0 None stk' loc' (pc' - length (compE2 obj)) xcp'"
	apply -
	apply(rule exec_meth_drop_xt)
	apply(simp add: compxEs2_size_convs compxEs2_stack_xlift_convs)
	apply(auto simp add: stack_xlift_compxE2)
	done
      from IHparams[OF this] PC obtain stk'' where stk': "stk' = stk'' @ v # STK"
	and exec': "exec_meth (compP2 P) (compEs2 ps) (compxEs2 ps 0 0) h ([], loc, 0, None) ta h' (stk'', loc', PC, xcp')"
	by auto
      from exec' have "exec_meth (compP2 P) ((compE2 obj @ compEs2 ps) @ [Invoke M' (length ps)]) (compxE2 obj 0 0 @ shift (length (compE2 obj)) (stack_xlift (length [v]) (compxEs2 ps 0 0))) h ([] @ [v], loc, length (compE2 obj) + 0, None) ta h' (stk'' @ [v], loc', length (compE2 obj) + PC, xcp')"
	apply -
	apply(rule exec_meth_append)
	apply(rule append_exec_meth_xt)
	apply(erule exec_meth_stk_offer)
	by(auto)
      thus ?thesis using stk' PC by(clarsimp simp add: shift_compxEs2 stack_xlift_compxEs2 add_ac)
    next
      case Nil
      with exec pc show ?thesis 
	by(force elim!: exec_meth.cases intro!: exec_meth.intros simp add: split_beta extRet2JVM_def[folded Datatype.sum_case_def] split: split_if_asm sum.split_asm)
    qed
  qed
next
  case (bisim1CallParams ps n ps' xs stk loc pc xcp obj M' v)
  note bisimParam = `P,ps,n,h \<turnstile> (ps',xs) [\<leftrightarrow>] (stk,loc,pc,xcp)`
  note IHparam = `\<And>stk' loc' pc' xcp' STK. ?execs ps stk STK loc pc xcp stk' loc' pc' xcp'
             \<Longrightarrow> ?concls ps stk STK loc pc xcp stk' loc' pc' xcp'`
  note exec = `?exec (obj\<bullet>M'(ps)) (stk @ [v]) STK loc (length (compE2 obj) + pc) xcp stk' loc' pc' xcp'`
  show ?case
  proof(cases ps)
    case Nil
    with bisimParam have "pc = 0" "xcp = None" by(auto elim: bisims1.cases)
    with exec Nil show ?thesis 
      apply(auto elim!: exec_meth.cases intro!: exec_meth.intros simp add: split_beta extRet2JVM_def[folded Datatype.sum_case_def] split: split_if_asm sum.split_asm)
      apply(force simp add: neq_Nil_conv intro: exec_meth.intros)+
      done
  next
    case Cons
    from bisimParam have pc: "pc \<le> length (compEs2 ps)" by(rule bisims1_pc_length_compEs2)
    show ?thesis
    proof(cases "pc < length (compEs2 ps)")
      case True
      from exec have "exec_meth (compP2 P) ((compE2 obj @ compEs2 ps) @ [Invoke M' (length ps)])
     (stack_xlift (length STK) (compxE2 obj 0 0) @ shift (length (compE2 obj)) (stack_xlift (length (v # STK)) (compxEs2 ps 0 0)))
     h (stk @ v # STK, loc, length (compE2 obj) + pc, xcp) ta h' (stk', loc', pc', xcp')"
	by(simp add: compxEs2_size_convs compxEs2_stack_xlift_convs)
      hence exec': "exec_meth (compP2 P) (compE2 obj @ compEs2 ps) (stack_xlift (length STK) (compxE2 obj 0 0) @
      shift (length (compE2 obj)) (stack_xlift (length (v # STK)) (compxEs2 ps 0 0)))
      h (stk @ v # STK, loc, length (compE2 obj) + pc, xcp) ta h' (stk', loc', pc', xcp')"
	by(rule exec_meth_take)(simp add: True)
      hence "?execs ps stk (v # STK) loc pc xcp stk' loc' (pc' - length (compE2 obj)) xcp'"
	by(rule exec_meth_drop_xt)(auto simp add: stack_xlift_compxE2)
      from IHparam[OF this] obtain stk'' where stk': "stk' = stk'' @ v # STK"
	and exec'': "exec_meth (compP2 P) (compEs2 ps) (compxEs2 ps 0 0) h (stk, loc, pc, xcp) ta h' (stk'', loc', pc' - length (compE2 obj), xcp')" by blast
      from exec'' have "exec_meth (compP2 P) (compEs2 ps) (stack_xlift (length [v]) (compxEs2 ps 0 0)) h (stk @ [v], loc, pc, xcp) ta h' (stk'' @ [v], loc', pc' - length (compE2 obj), xcp')"
	by(rule exec_meth_stk_offer)
      hence "exec_meth (compP2 P) (compE2 obj @ compEs2 ps) (compxE2 obj 0 0 @ shift (length (compE2 obj)) (stack_xlift (length [v]) (compxEs2 ps 0 0)))
 h (stk @ [v], loc, length (compE2 obj) + pc, xcp) ta h' (stk'' @ [v], loc', length (compE2 obj) + (pc' - length (compE2 obj)), xcp')"
	by(rule append_exec_meth_xt) auto
      hence "exec_meth (compP2 P) ((compE2 obj @ compEs2 ps) @ [Invoke M' (length ps)])
     (compxE2 obj 0 0 @ shift (length (compE2 obj)) (stack_xlift (length [v]) (compxEs2 ps 0 0)))
 h (stk @ [v], loc, length (compE2 obj) + pc, xcp) ta h' (stk'' @ [v], loc', length (compE2 obj) + (pc' - length (compE2 obj)), xcp')"
	by(rule exec_meth_append)
      moreover from exec' have "pc' \<ge> length (compE2 obj)"
	by(rule exec_meth_drop_xt_pc)(auto simp add: stack_xlift_compxE2)
      ultimately show ?thesis using stk'
	by(auto simp add: shift_compxEs2 stack_xlift_compxEs2)
    next
      case False
      with pc have pc: "pc = length (compEs2 ps)" by simp
      with bisimParam obtain vs where "stk = vs" "length vs = length ps" "xcp = None"
	by(auto dest: bisims1_pc_length_compEs2D)
      with exec pc Cons show ?thesis
	apply(auto elim!: exec_meth.cases intro!: exec_meth.intros simp add: split_beta extRet2JVM_def[folded Datatype.sum_case_def] split: split_if_asm sum.split_asm)
	apply(force simp add: neq_Nil_conv intro: exec_meth.intros)+
	done
    qed
  qed
next
  case (bisim1CallThrowObj obj n a xs stk loc pc ps M')
  note bisim = `P,obj,n,h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)`
  note IH = `\<And>stk' loc' pc' xcp' STK. ?exec obj stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'
             \<Longrightarrow> ?concl obj stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'`
  note exec = `?exec (obj\<bullet>M'(ps)) stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'`
  from bisim have "pc < length (compE2 obj)" and [simp]: "xs = loc" by(auto dest: bisim1_ThrowD)
  with exec have "?exec obj stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'"
    by(simp add: compxEs2_size_convs compxEs2_stack_xlift_convs)(erule exec_meth_take_xt)
  from IH[OF this] show ?case by auto
next
  case (bisim1CallThrowParams ps n vs a ps' xs stk loc pc obj M' v)
  note bisim = `P,ps,n,h \<turnstile> (map Val vs @ Throw a # ps',xs) [\<leftrightarrow>] (stk,loc,pc,\<lfloor>a\<rfloor>)`
  note IH = `\<And>stk' loc' pc' xcp' STK. ?execs ps stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'
             \<Longrightarrow> ?concls ps stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'`
  note exec = `?exec (obj\<bullet>M'(ps)) (stk @ [v]) STK loc (length (compE2 obj) + pc) \<lfloor>a\<rfloor> stk' loc' pc' xcp'`
  from bisim have pc: "pc < length (compEs2 ps)" "loc = xs" by(auto dest: bisims1_ThrowD)
  from exec have "exec_meth (compP2 P) ((compE2 obj @ compEs2 ps) @ [Invoke M' (length ps)])
     (stack_xlift (length STK) (compxE2 obj 0 0) @ shift (length (compE2 obj)) (stack_xlift (length (v # STK)) (compxEs2 ps 0 0)))
     h (stk @ v # STK, loc, length (compE2 obj) + pc, \<lfloor>a\<rfloor>) ta h' (stk', loc', pc', xcp')"
    by(simp add: compxEs2_size_convs compxEs2_stack_xlift_convs)
  hence exec': "exec_meth (compP2 P) (compE2 obj @ compEs2 ps) (stack_xlift (length STK) (compxE2 obj 0 0) @
      shift (length (compE2 obj)) (stack_xlift (length (v # STK)) (compxEs2 ps 0 0)))
     h (stk @ v # STK, loc, length (compE2 obj) + pc, \<lfloor>a\<rfloor>) ta h' (stk', loc', pc', xcp')"
    by(rule exec_meth_take)(simp add: pc)
  hence "?execs ps stk (v # STK) loc pc \<lfloor>a\<rfloor> stk' loc' (pc' - length (compE2 obj)) xcp'"
    by(rule exec_meth_drop_xt)(auto simp add: stack_xlift_compxE2)
  from IH[OF this] obtain stk'' where stk': "stk' = stk'' @ v # STK"
    and exec'': "exec_meth (compP2 P) (compEs2 ps) (compxEs2 ps 0 0) h (stk, loc, pc, \<lfloor>a\<rfloor>) ta h' (stk'', loc', pc' - length (compE2 obj), xcp')" by auto
  from exec'' have "exec_meth (compP2 P) ((compE2 obj @ compEs2 ps) @ [Invoke M' (length ps)])
     (compxE2 obj 0 0 @ shift (length (compE2 obj)) (stack_xlift (length [v]) (compxEs2 ps 0 0)))
     h (stk @ [v], loc, length (compE2 obj) + pc, \<lfloor>a\<rfloor>) ta h' (stk'' @ [v], loc', length (compE2 obj) + (pc' - length (compE2 obj)), xcp')"
    apply - 
    apply(rule exec_meth_append)
    apply(rule append_exec_meth_xt)
    apply(erule exec_meth_stk_offer)
    apply auto
    done
  moreover from exec' have "pc' \<ge> length (compE2 obj)"
    by(rule exec_meth_drop_xt_pc)(auto simp add: stack_xlift_compxE2)
  ultimately show ?case using stk' by(auto simp add: compxEs2_size_convs compxEs2_stack_xlift_convs)
next
  case bisim1CallThrow thus ?case
    by(auto elim!: exec_meth.cases dest: match_ex_table_pcsD simp add: stack_xlift_compxEs2 stack_xlift_compxE2)
next
  case bisim1BlockSome1 thus ?case
    by(fastsimp elim: exec_meth.cases intro: exec_meth.intros)
next
  case bisim1BlockSome2 thus ?case
    by(fastsimp elim: exec_meth.cases intro: exec_meth.intros)
next
  case (bisim1BlockSome3 e V e' xs v stk loc pc xcp T)
  note IH = `\<And>stk' loc' pc' xcp' STK. ?exec e stk STK loc pc xcp stk' loc' pc' xcp'
             \<Longrightarrow> ?concl e stk STK loc pc xcp stk' loc' pc' xcp'`
  note exec = `?exec {V:T=\<lfloor>v\<rfloor>; e}\<^bsub>False\<^esub> stk STK loc (Suc (Suc pc)) xcp stk' loc' pc' xcp'`
  hence exec': "exec_meth (compP2 P) ([Push v, Store V] @ compE2 e)
     (shift (length [Push v, Store V]) (stack_xlift (length STK) (compxE2 e 0 0))) h (stk @ STK, loc, length [Push v, Store V] + pc, xcp) ta h' (stk', loc', pc', xcp')"
    by(simp add: compxE2_size_convs)
  hence "?exec e stk STK loc pc xcp stk' loc' (pc' - length [Push v, Store V]) xcp'"
    by(rule exec_meth_drop) auto
  from IH[OF this] obtain stk'' where stk': "stk' = stk'' @ STK"
    and exec'': "exec_meth (compP2 P) (compE2 e) (compxE2 e 0 0) h (stk, loc, pc, xcp) ta
      h' (stk'', loc', pc' - length [Push v, Store V], xcp')" by auto
  from exec'' have "exec_meth (compP2 P) ([Push v, Store V] @ compE2 e)
     (shift (length [Push v, Store V]) (compxE2 e 0 0)) h (stk, loc, length [Push v, Store V] + pc, xcp) ta h' (stk'', loc', length [Push v, Store V] + (pc' - length [Push v, Store V]), xcp')"
    by(rule append_exec_meth) auto
  moreover from exec' have "pc' \<ge> length [Push v, Store V]"
    by(rule exec_meth_drop_pc)(auto simp add: stack_xlift_compxE2)
  hence "Suc (Suc (pc' - Suc (Suc 0))) = pc'" by(simp)
  ultimately show ?case using stk' by(auto simp add: compxE2_size_convs)
next
  case (bisim1BlockSome4 e V e' xs stk loc pc xcp T v)
  note IH = `\<And>stk' loc' pc' xcp' STK. ?exec e stk STK loc pc xcp stk' loc' pc' xcp'
             \<Longrightarrow> ?concl e stk STK loc pc xcp stk' loc' pc' xcp'`
  note bisim = `P,e,Suc V,h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, xcp)`
  note exec = `?exec {V:T=\<lfloor>v\<rfloor>; e}\<^bsub>False\<^esub> stk STK loc (Suc (Suc pc)) xcp stk' loc' pc' xcp'`
  hence exec': "exec_meth (compP2 P) ([Push v, Store V] @ compE2 e)
     (shift (length [Push v, Store V]) (stack_xlift (length STK) (compxE2 e 0 0))) h (stk @ STK, loc, length [Push v, Store V] + pc, xcp) ta h' (stk', loc', pc', xcp')"
    by(simp add: compxE2_size_convs)
  hence "?exec e stk STK loc pc xcp stk' loc' (pc' - length [Push v, Store V]) xcp'"
    by(rule exec_meth_drop) auto
  from IH[OF this] obtain stk'' where stk': "stk' = stk'' @ STK"
    and exec'': "exec_meth (compP2 P) (compE2 e) (compxE2 e 0 0) h (stk, loc, pc, xcp) ta
      h' (stk'', loc', pc' - length [Push v, Store V], xcp')" by auto
  from exec'' have "exec_meth (compP2 P) ([Push v, Store V] @ compE2 e)
     (shift (length [Push v, Store V]) (compxE2 e 0 0)) h (stk, loc, length [Push v, Store V] + pc, xcp) ta h' (stk'', loc', length [Push v, Store V] + (pc' - length [Push v, Store V]), xcp')"
    by(rule append_exec_meth) auto
  moreover from exec' have "pc' \<ge> length [Push v, Store V]"
    by(rule exec_meth_drop_pc)(auto simp add: stack_xlift_compxE2)
  hence "Suc (Suc (pc' - Suc (Suc 0))) = pc'" by(simp)
  ultimately show ?case using stk' by(auto simp add: compxE2_size_convs)
next
  case (bisim1BlockThrowSome e V a xs stk loc pc T v)
  note IH = `\<And>stk' loc' pc' xcp' STK. ?exec e stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'
             \<Longrightarrow> ?concl e stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'`
  note exec = `?exec {V:T=\<lfloor>v\<rfloor>; e}\<^bsub>False\<^esub> stk STK loc (Suc (Suc pc)) \<lfloor>a\<rfloor> stk' loc' pc' xcp'`
  hence exec': "exec_meth (compP2 P) ([Push v, Store V] @ compE2 e)
     (shift (length [Push v, Store V]) (stack_xlift (length STK) (compxE2 e 0 0))) h (stk @ STK, loc, length [Push v, Store V] + pc, \<lfloor>a\<rfloor>) ta h' (stk', loc', pc', xcp')"
    by(simp add: compxE2_size_convs)
  hence "?exec e stk STK loc pc \<lfloor>a\<rfloor> stk' loc' (pc' - length [Push v, Store V]) xcp'"
    by(rule exec_meth_drop) auto
  from IH[OF this] obtain stk'' where stk': "stk' = stk'' @ STK"
    and exec'': "exec_meth (compP2 P) (compE2 e) (compxE2 e 0 0) h (stk, loc, pc, \<lfloor>a\<rfloor>) ta
      h' (stk'', loc', pc' - length [Push v, Store V], xcp')" by auto
  from exec'' have "exec_meth (compP2 P) ([Push v, Store V] @ compE2 e)
     (shift (length [Push v, Store V]) (compxE2 e 0 0)) h (stk, loc, length [Push v, Store V] + pc, \<lfloor>a\<rfloor>) ta h' (stk'', loc', length [Push v, Store V] + (pc' - length [Push v, Store V]), xcp')"
    by(rule append_exec_meth) auto
  moreover from exec' have "pc' \<ge> length [Push v, Store V]"
    by(rule exec_meth_drop_pc)(auto simp add: stack_xlift_compxE2)
  hence "Suc (Suc (pc' - Suc (Suc 0))) = pc'" by(simp)
  ultimately show ?case using stk' by(auto simp add: compxE2_size_convs)
next
  case bisim1BlockNone thus ?case
    by(fastsimp elim: exec_meth.cases intro: exec_meth.intros)
next
  case bisim1BlockThrowNone thus ?case
    by(fastsimp elim: exec_meth.cases intro: exec_meth.intros)
next
  case (bisim1Sync1 e1 V e1' xs stk loc pc xcp e2)
  note bisim = `P,e1,V,h \<turnstile> (e1', xs) \<leftrightarrow> (stk, loc, pc, xcp)`
  note IH = `\<And>stk' loc' pc' xcp' STK. ?exec e1 stk STK loc pc xcp stk' loc' pc' xcp'
             \<Longrightarrow> ?concl e1 stk STK loc pc xcp stk' loc' pc' xcp'`
  note exec = `?exec (sync\<^bsub>V\<^esub> (e1) e2) stk STK loc pc xcp stk' loc' pc' xcp'`
  from bisim have pc: "pc \<le> length (compE2 e1)" by(rule bisim1_pc_length_compE2)
  show ?case
  proof(cases "pc < length (compE2 e1)")
    case True
    from exec have "exec_meth (compP2 P)
      (compE2 e1 @ (Store V # Load V # MEnter # compE2 e2 @ [Load V, MExit, Goto 4, Load V, MExit, Throw]))
      (stack_xlift (length STK) (compxE2 e1 0 0) @ shift (length (compE2 e1)) (stack_xlift (length STK) (compxE2 e2 3 0) @
       stack_xlift (length STK) [(3, 3 + length (compE2 e2), Throwable, 6 + length (compE2 e2), 0)]))
      h (stk @ STK, loc, pc, xcp) ta h' (stk', loc', pc', xcp')"
      by(simp add: shift_compxE2 stack_xlift_compxE2 add_ac)
    hence "?exec e1 stk STK loc pc xcp stk' loc' pc' xcp'"
      by(rule exec_meth_take_xt)(rule True)
    from IH[OF this] obtain stk'' where stk': "stk' = stk'' @ STK"
      and exec': "exec_meth (compP2 P) (compE2 e1) (compxE2 e1 0 0) h (stk, loc, pc, xcp) ta h' (stk'', loc', pc', xcp')"
      by blast
    from exec' have "exec_meth (compP2 P) (compE2 e1 @ (Store V # Load V # MEnter # compE2 e2 @ [Load V, MExit, Goto 4, Load V, MExit, Throw]))
      (compxE2 e1 0 0 @ shift (length (compE2 e1)) (compxE2 e2 3 0 @ [(3, 3 + length (compE2 e2), Throwable, 6 + length (compE2 e2), 0)]))
      h (stk, loc, pc, xcp) ta h' (stk'', loc', pc', xcp')"
      by(rule exec_meth_append_xt)
    thus ?thesis using stk' by(simp add: shift_compxE2 stack_xlift_compxE2 add_ac)
  next
    case False
    with pc have [simp]: "pc = length (compE2 e1)" by simp
    with bisim obtain v where "stk = [v]" "xcp = None" by(auto dest: bisim1_pc_length_compE2D)
    thus ?thesis using exec by(auto elim!: exec_meth.cases intro!: exec_meth.intros)
  qed
next
  case bisim1Sync2 thus ?case
    by(fastsimp elim!: exec_meth.cases intro!: exec_meth.intros)
next
  case bisim1Sync3 thus ?case
    by(fastsimp elim!: exec_meth.cases intro!: exec_meth.intros split: split_if_asm)
next
  case (bisim1Sync4 e2 V e2' xs stk loc pc xcp e1 a)
  note IH = `\<And>stk' loc' pc' xcp' STK. ?exec e2 stk STK loc pc xcp stk' loc' pc' xcp'
             \<Longrightarrow> ?concl e2 stk STK loc pc xcp stk' loc' pc' xcp'`
  note bisim = `P,e2,Suc V,h \<turnstile> (e2', xs) \<leftrightarrow> (stk, loc, pc, xcp)`
  note exec = `?exec (sync\<^bsub>V\<^esub> (e1) e2) stk STK loc (Suc (Suc (Suc (length (compE2 e1) + pc)))) xcp stk' loc' pc' xcp'`
  from bisim have pc: "pc \<le> length (compE2 e2)" by(rule bisim1_pc_length_compE2)
  show ?case
  proof(cases "pc < length (compE2 e2)")
    case True
    from exec have exec': "exec_meth (compP2 P) ((compE2 e1 @ [Store V, Load V, MEnter]) @ compE2 e2 @ [Load V, MExit, Goto 4, Load V, MExit, Throw])
     (stack_xlift (length STK) (compxE2 e1 0 0) @ shift (length (compE2 e1 @ [Store V, Load V, MEnter])) (stack_xlift (length STK) (compxE2 e2 0 0) @
      [(0, length (compE2 e2), Throwable, 3 + length (compE2 e2), length STK)]))
     h (stk @ STK, loc, length (compE2 e1 @ [Store V, Load V, MEnter]) + pc, xcp) ta h' (stk', loc', pc', xcp')"
      by(simp add: stack_xlift_compxE2 shift_compxE2 nat_number add_ac)
    hence exec'': "exec_meth (compP2 P) (compE2 e2 @ [Load V, MExit, Goto 4, Load V, MExit, Throw])
      (stack_xlift (length STK) (compxE2 e2 0 0) @ [(0, length (compE2 e2), Throwable, 3 + length (compE2 e2), length STK)])
     h (stk @ STK, loc, pc, xcp) ta h' (stk', loc', pc' - length (compE2 e1 @ [Store V, Load V, MEnter]), xcp')"
      by(rule exec_meth_drop_xt[where n=1])(auto simp add: stack_xlift_compxE2)
    from exec' have pc': "pc' \<ge> length (compE2 e1 @ [Store V, Load V, MEnter])"
      by(rule exec_meth_drop_xt_pc[where n'=1])(auto simp add: stack_xlift_compxE2)
    hence pc'': "(Suc (Suc (Suc (pc' - Suc (Suc (Suc 0)))))) = pc'" by simp
    show ?thesis
    proof(cases xcp)
      case None
      from exec'' None True
      have "?exec e2 stk STK loc pc xcp stk' loc' (pc' - length (compE2 e1 @ [Store V, Load V, MEnter])) xcp'"
	apply -
	apply(erule exec_meth.cases)
	apply(cases "compE2 e2 ! pc")
	apply(fastsimp simp add: is_Ref_def elim!: is_ArrE intro: exec_meth.intros split: split_if_asm)+
	done
      from IH[OF this] obtain stk'' where stk: "stk' = stk'' @ STK"
	and exec''': "exec_meth (compP2 P) (compE2 e2) (compxE2 e2 0 0) h (stk, loc, pc, xcp)
      ta h' (stk'', loc', pc' - length (compE2 e1 @ [Store V, Load V, MEnter]), xcp')" by blast
      from exec''' have "exec_meth (compP2 P) (compE2 e2 @ [Load V, MExit, Goto 4, Load V, MExit, Throw])
      (compxE2 e2 0 0 @ [(0, length (compE2 e2), Throwable, 3 + length (compE2 e2), 0)])
     h (stk, loc, pc, xcp) ta h' (stk'', loc', pc' - length (compE2 e1 @ [Store V, Load V, MEnter]), xcp')"
	by(rule exec_meth_append_xt)
      hence "exec_meth (compP2 P) ((compE2 e1 @ [Store V, Load V, MEnter]) @ compE2 e2 @ [Load V, MExit, Goto 4, Load V, MExit, Throw])
      (compxE2 e1 0 0 @ shift (length (compE2 e1 @ [Store V, Load V, MEnter])) (compxE2 e2 0 0 @ [(0, length (compE2 e2), Throwable, 3 + length (compE2 e2), 0)]))
     h (stk, loc, length (compE2 e1 @ [Store V, Load V, MEnter]) + pc, xcp) ta h' (stk'', loc', length (compE2 e1 @ [Store V, Load V, MEnter]) + (pc' - length (compE2 e1 @ [Store V, Load V, MEnter])), xcp')"
	by(rule append_exec_meth_xt[where n=1])(auto)
      thus ?thesis using stk pc' pc'' by(simp add: nat_number shift_compxE2 add_ac)
    next
      case (Some a)
      with exec'' have [simp]: "h' = h" "xcp' = None" "loc' = loc" "ta = \<epsilon>"
	by(auto elim!: exec_meth.cases simp add: match_ex_table_append
           split: split_if_asm dest!: match_ex_table_stack_xliftD)
      show ?thesis
      proof(cases "match_ex_table (compP2 P) (cname_of h a) pc (compxE2 e2 0 0)")
	case None
	with Some exec'' True have [simp]: "stk' = Addr a # STK"
	  and pc': "pc' = length (compE2 e1) + length (compE2 e2) + 6"
	  by(auto elim!: exec_meth.cases simp add: match_ex_table_append
                  split: split_if_asm dest!: match_ex_table_stack_xliftD)
	with exec'' Some None
	have "exec_meth (compP2 P) (compE2 e2 @ [Load V, MExit, Goto 4, Load V, MExit, Throw])
	(compxE2 e2 0 0 @ [(0, length (compE2 e2), Throwable, 3 + length (compE2 e2), 0)])
	h (stk, loc, pc, \<lfloor>a\<rfloor>) \<epsilon> h (Addr a # drop (length stk - 0) stk, loc, pc' - length (compE2 e1 @ [Store V, Load V, MEnter]), None)"
	  by -(rule exec_catch, auto elim!: exec_meth.cases simp add: match_ex_table_append matches_ex_entry_def
                                     split: split_if_asm dest!: match_ex_table_stack_xliftD)
	hence "exec_meth (compP2 P) ((compE2 e1 @ [Store V, Load V, MEnter]) @ compE2 e2 @ [Load V, MExit, Goto 4, Load V, MExit, Throw])
	(compxE2 e1 0 0 @ shift (length (compE2 e1 @ [Store V, Load V, MEnter])) (compxE2 e2 0 0 @ [(0, length (compE2 e2), Throwable, 3 + length (compE2 e2), 0)]))
	h (stk, loc, length (compE2 e1 @ [Store V, Load V, MEnter]) + pc, \<lfloor>a\<rfloor>) \<epsilon> h (Addr a # drop (length stk - 0) stk, loc,
	length (compE2 e1 @ [Store V, Load V, MEnter]) + (pc' - length (compE2 e1 @ [Store V, Load V, MEnter])), None)"
	  by(rule append_exec_meth_xt[where n=1])(auto)
	with pc' Some show ?thesis by(simp add: nat_number shift_compxE2 add_ac)
      next
	case (Some pcd)
	with `xcp = \<lfloor>a\<rfloor>` exec'' True
	have "exec_meth (compP2 P) (compE2 e2) (compxE2 e2 0 0)
   h (stk, loc, pc, \<lfloor>a\<rfloor>) \<epsilon> h (Addr a # drop (length stk - snd pcd) stk, loc, pc' - length (compE2 e1 @ [Store V, Load V, MEnter]), None)"
	  apply -
	  apply(rule exec_catch)
	  apply(auto elim!: exec_meth.cases simp add: match_ex_table_append split: split_if_asm
	             dest!: match_ex_table_stack_xliftD)
	  done
	hence "exec_meth (compP2 P) (compE2 e2 @ [Load V, MExit, Goto 4, Load V, MExit, Throw]) (compxE2 e2 0 0 @ [(0, length (compE2 e2), Throwable, 3 + length (compE2 e2), 0)])
   h (stk, loc, pc, \<lfloor>a\<rfloor>) \<epsilon> h (Addr a # drop (length stk - snd pcd) stk, loc, pc' - length (compE2 e1 @ [Store V, Load V, MEnter]), None)"
	  by(rule exec_meth_append_xt)
	hence "exec_meth (compP2 P) ((compE2 e1 @ [Store V, Load V, MEnter]) @ compE2 e2 @ [Load V, MExit, Goto 4, Load V, MExit, Throw]) 
              (compxE2 e1 0 0 @ shift (length (compE2 e1 @ [Store V, Load V, MEnter])) (compxE2 e2 0 0 @ [(0, length (compE2 e2), Throwable, 3 + length (compE2 e2), 0)]))
   h (stk, loc, length (compE2 e1 @ [Store V, Load V, MEnter]) + pc, \<lfloor>a\<rfloor>) \<epsilon> h (Addr a # drop (length stk - snd pcd) stk, loc, length (compE2 e1 @ [Store V, Load V, MEnter]) + (pc' - length (compE2 e1 @ [Store V, Load V, MEnter])), None)"
	  by(rule append_exec_meth_xt[where n=1])(auto)
	moreover from Some `xcp = \<lfloor>a\<rfloor>` exec'' True pc'
	have "pc' = length (compE2 e1) + 3 + fst pcd" "stk' = Addr a # drop (length stk - snd pcd) stk @ STK"
	  by(auto elim!: exec_meth.cases dest!: match_ex_table_stack_xliftD simp: match_ex_table_append split: split_if_asm)
	ultimately show ?thesis using `xcp = \<lfloor>a\<rfloor>` by(auto simp add: nat_number shift_compxE2 add_ac)
      qed
    qed
  next
    case False
    with pc have [simp]: "pc = length (compE2 e2)" by simp
    with exec show ?thesis
      by(auto elim!: exec_meth.cases intro!: exec_meth.intros split: split_if_asm simp add: match_ex_table_append_not_pcs nat_number)(simp_all add: matches_ex_entry_def)
  qed
next
  case bisim1Sync5 thus ?case
    by(fastsimp elim: exec_meth.cases intro: exec_meth.intros split: split_if_asm)
next
  case bisim1Sync6 thus ?case  
    by(fastsimp elim: exec_meth.cases intro: exec_meth.intros split: split_if_asm)	
next
  case bisim1Sync7 thus ?case
    by(fastsimp elim: exec_meth.cases intro: exec_meth.intros split: split_if_asm)
next
  case bisim1Sync8 thus ?case
    by(fastsimp elim: exec_meth.cases intro: exec_meth.intros split: split_if_asm)
next
  case (bisim1Sync9 e1 V e2 a xs)
  note exec = `?exec (sync\<^bsub>V\<^esub> (e1) e2) [Addr a] STK xs (8 + length (compE2 e1) + length (compE2 e2)) None stk' loc' pc' xcp'`
  let ?pre = "compE2 e1 @ Store V # Load V # MEnter # compE2 e2 @ [Load V, MExit, Goto 4, Load V, MExit]"
  from exec have exec': "exec_meth (compP2 P) (?pre @ [Throw]) (stack_xlift (length STK) (compxE2 (sync\<^bsub>V\<^esub> (e1) e2) 0 0) @ shift (length ?pre) []) h (Addr a # STK, xs, length ?pre + 0, None) ta h' (stk', loc', pc', xcp')"
    by(simp add: nat_number)
  hence "exec_meth (compP2 P) [Throw] [] h (Addr a # STK, xs, 0, None) ta h' (stk', loc', pc' - length ?pre, xcp')"
    by(rule exec_meth_drop_xt)(auto simp add: stack_xlift_compxE2)
  moreover from exec' have "pc' = 8 + length (compE2 e1) + length (compE2 e2)" "stk' = Addr a # STK"
    by(auto elim!: exec_meth.cases)
  ultimately show ?case by(fastsimp elim!: exec_meth.cases intro: exec_meth.intros)
next
  case (bisim1Sync10 e1 V e2 a xs)
  note exec = `?exec (sync\<^bsub>V\<^esub> (e1) e2) [Addr a] STK xs (8 + length (compE2 e1) + length (compE2 e2)) \<lfloor>a\<rfloor> stk' loc' pc' xcp'`
  hence "match_ex_table (compP2 P) (cname_of h a) (8 + length (compE2 e1) + length (compE2 e2)) (stack_xlift (length STK) (compxE2 (sync\<^bsub>V\<^esub> (e1) e2) 0 0)) \<noteq> None"
    by(rule exec_meth.cases) auto
  hence False by(auto split: split_if_asm simp add: match_ex_table_append_not_pcs)(simp add: matches_ex_entry_def)
  thus ?case ..
next
  case (bisim1Sync11 e1 V e2 xs)
  note exec = `?exec (sync\<^bsub>V\<^esub> (e1) e2) [Null] STK xs (Suc (Suc (length (compE2 e1)))) \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor> stk' loc' pc' xcp'`
  hence "match_ex_table (compP2 P) (cname_of h (addr_of_sys_xcpt NullPointer)) (2 + length (compE2 e1)) (stack_xlift (length STK) (compxE2 (sync\<^bsub>V\<^esub> (e1) e2) 0 0)) \<noteq> None"
    by(rule exec_meth.cases)(auto split: split_if_asm)
  hence False by(auto split: split_if_asm simp add: match_ex_table_append_not_pcs)(simp add: matches_ex_entry_def)
  thus ?case ..
next
  case (bisim1SyncThrow e1 V a xs stk loc pc e2)
  note exec = `?exec (sync\<^bsub>V\<^esub> (e1) e2) stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'`
  note IH = `\<And>stk' loc' pc' xcp' STK. ?exec e1 stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'
             \<Longrightarrow> ?concl e1 stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'`
  note bisim = `P,e1,V,h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)`
  from bisim have pc: "pc < length (compE2 e1)"
    and [simp]: "loc = xs" by(auto dest: bisim1_ThrowD)
  from exec have "exec_meth (compP2 P) (compE2 e1 @ Store V # Load V #  MEnter # compE2 e2 @ [Load V, MExit, Goto 4, Load V, MExit, Throw])
     (stack_xlift (length STK) (compxE2 e1 0 0) @ shift (length (compE2 e1)) (stack_xlift (length STK) (compxE2 e2 3 0) @
      [(3, 3 + length (compE2 e2), Throwable, 6 + length (compE2 e2), length STK)]))
     h (stk @ STK, loc, pc, \<lfloor>a\<rfloor>) ta h' (stk', loc', pc', xcp')"
    by(simp add: shift_compxE2 stack_xlift_compxE2 add_ac)
  hence "?exec e1 stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'"
    by(rule exec_meth_take_xt)(rule pc)
  from IH[OF this] show ?case by auto
next
  case (bisim1Seq1 e1 n e1' xs stk loc pc xcp e2)
  note bisim1 = `P,e1,n,h \<turnstile> (e1', xs) \<leftrightarrow> (stk, loc, pc, xcp)`
  note IH = `\<And>stk' loc' pc' xcp' STK. ?exec e1 stk STK loc pc xcp stk' loc' pc' xcp'
             \<Longrightarrow> ?concl e1 stk STK loc pc xcp stk' loc' pc' xcp'`
  note exec = `?exec (e1;;e2) stk STK loc pc xcp stk' loc' pc' xcp'`
  from bisim1 have pc: "pc \<le> length (compE2 e1)" by(rule bisim1_pc_length_compE2)
  show ?case
  proof(cases "pc < length (compE2 e1)")
    case True
    from exec have "exec_meth (compP2 P) (compE2 e1 @ Pop # compE2 e2) (stack_xlift (length STK) (compxE2 e1 0 0) @
      shift (length (compE2 e1)) (stack_xlift (length STK) (compxE2 e2 (Suc 0) 0)))
     h (stk @ STK, loc, pc, xcp) ta h' (stk', loc', pc', xcp')"
      by(simp add: shift_compxE2 stack_xlift_compxE2)
    hence "?exec e1 stk STK loc pc xcp stk' loc' pc' xcp'"
      by(rule exec_meth_take_xt)(rule True)
    from IH[OF this] show ?thesis by auto
  next
    case False
    with pc have [simp]: "pc = length (compE2 e1)" by simp
    with bisim1 obtain v where "xcp = None" "stk = [v]" by(auto dest: bisim1_pc_length_compE2D)
    with exec show ?thesis by(fastsimp elim: exec_meth.cases intro: exec_meth.intros)
  qed
next
  case (bisim1SeqThrow1 e1 n a xs stk loc pc e2)
  note bisim1 = `P,e1,n,h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)`
  note IH = `\<And>stk' loc' pc' xcp' STK. ?exec e1 stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'
             \<Longrightarrow> ?concl e1 stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'`
  note exec = `?exec (e1;;e2) stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'`
  from bisim1 have pc: "pc < length (compE2 e1)" by(auto dest: bisim1_ThrowD)
  from exec have "exec_meth (compP2 P) (compE2 e1 @ Pop # compE2 e2) (stack_xlift (length STK) (compxE2 e1 0 0) @
      shift (length (compE2 e1)) (stack_xlift (length STK) (compxE2 e2 (Suc 0) 0)))
     h (stk @ STK, loc, pc, \<lfloor>a\<rfloor>) ta h' (stk', loc', pc', xcp')"
    by(simp add: shift_compxE2 stack_xlift_compxE2)
  hence "?exec e1 stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'"
    by(rule exec_meth_take_xt)(rule pc)
  from IH[OF this] show ?case by(fastsimp elim: exec_meth.cases intro: exec_meth.intros)
next
  case (bisim1Seq2 e2 n e2' xs stk loc pc xcp e1)
  note bisim2 = `P,e2,n,h \<turnstile> (e2', xs) \<leftrightarrow> (stk, loc, pc, xcp)`
  note IH = `\<And>stk' loc' pc' xcp' STK. ?exec e2 stk STK loc pc xcp stk' loc' pc' xcp'
             \<Longrightarrow> ?concl e2 stk STK loc pc xcp stk' loc' pc' xcp'`
  note exec = `?exec (e1;;e2) stk STK loc (Suc (length (compE2 e1) + pc)) xcp stk' loc' pc' xcp'`
  from bisim2 have pc: "pc \<le> length (compE2 e2)" by(rule bisim1_pc_length_compE2)
  show ?case
  proof(cases "pc < length (compE2 e2)")
    case False
    with pc have [simp]: "pc = length (compE2 e2)" by simp
    from bisim2 have "xcp = None" by(auto dest: bisim1_pc_length_compE2D)
    with exec have False by(auto elim: exec_meth.cases)
    thus ?thesis ..
  next
    case True
    from exec have exec':
      "exec_meth (compP2 P) ((compE2 e1 @ [Pop]) @ compE2 e2) (stack_xlift (length STK) (compxE2 e1 0 0) @
      shift (length (compE2 e1 @ [Pop])) (stack_xlift (length STK) (compxE2 e2 0 0)))
     h (stk @ STK, loc, length ((compE2 e1) @ [Pop]) + pc, xcp) ta h' (stk', loc', pc', xcp')"
      by(simp add: compxE2_size_convs)
    hence "?exec e2 stk STK loc pc xcp stk' loc' (pc' - length ((compE2 e1) @ [Pop])) xcp'"
      by(rule exec_meth_drop_xt)(auto simp add: stack_xlift_compxE2)
    from IH[OF this] obtain stk'' where stk': "stk' = stk'' @ STK"
      and exec'': "exec_meth (compP2 P) (compE2 e2) (compxE2 e2 0 0) h (stk, loc, pc, xcp)
      ta h' (stk'', loc', pc' - length (compE2 e1 @ [Pop]), xcp')" by auto
    from exec'' have "exec_meth (compP2 P) ((compE2 e1 @ [Pop]) @ compE2 e2) (compxE2 e1 0 0 @ shift (length (compE2 e1 @ [Pop])) (compxE2 e2 0 0))
     h (stk, loc, length ((compE2 e1) @ [Pop]) + pc, xcp) ta h' (stk'', loc', length ((compE2 e1) @ [Pop]) + (pc' - length ((compE2 e1) @ [Pop])), xcp')"
      by(rule append_exec_meth_xt) auto
    moreover from exec' have "pc' \<ge> length ((compE2 e1) @ [Pop])"
      by(rule exec_meth_drop_xt_pc)(auto simp add: stack_xlift_compxE2)
    ultimately show ?thesis using stk' by(auto simp add: shift_compxE2 stack_xlift_compxE2)
  qed
next
  case (bisim1Cond1 e n e' xs stk loc pc xcp e1 e2)
  note bisim = `P,e,n,h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, xcp)`
  note IH = `\<And>stk' loc' pc' xcp' STK. ?exec e stk STK loc pc xcp stk' loc' pc' xcp'
             \<Longrightarrow> ?concl e stk STK loc pc xcp stk' loc' pc' xcp'`
  note exec = `?exec (if (e) e1 else e2) stk STK loc pc xcp stk' loc' pc' xcp'`
  from bisim have pc: "pc \<le> length (compE2 e)" by(rule bisim1_pc_length_compE2)
  show ?case
  proof(cases "pc < length (compE2 e)")
    case True
    from exec have "exec_meth (compP2 P) (compE2 e @ IfFalse (2 + int (length (compE2 e1))) # compE2 e1 @ Goto (1 + int (length (compE2 e2))) # compE2 e2)
     (stack_xlift (length STK) (compxE2 e 0 0) @ shift (length (compE2 e)) (stack_xlift (length STK) (compxE2 e1 (Suc 0) 0) @
      stack_xlift (length STK) (compxE2 e2 (Suc (Suc (length (compE2 e1)))) 0)))
     h (stk @ STK, loc, pc, xcp) ta h' (stk', loc', pc', xcp')"
      by(simp add: stack_xlift_compxE2 shift_compxE2 add_ac)
    hence "?exec e stk STK loc pc xcp stk' loc' pc' xcp'"
      by(rule exec_meth_take_xt)(rule True)
    from IH[OF this] show ?thesis by auto
  next
    case False
    with pc have [simp]: "pc = length (compE2 e)" by simp
    from bisim obtain v where "stk = [v]" "xcp = None"
      by(auto dest: bisim1_pc_length_compE2D)
    with exec show ?thesis by(auto elim!: exec_meth.cases intro!: exec_meth.intros)
  qed
next
  case (bisim1CondThen e1 n e1' xs stk loc pc xcp e e2)
  note bisim = `P,e1,n,h \<turnstile> (e1', xs) \<leftrightarrow> (stk, loc, pc, xcp)`
  note IH = `\<And>stk' loc' pc' xcp' STK. ?exec e1 stk STK loc pc xcp stk' loc' pc' xcp'
             \<Longrightarrow> ?concl e1 stk STK loc pc xcp stk' loc' pc' xcp'`
  note exec = `?exec (if (e) e1 else e2) stk STK loc (Suc (length (compE2 e) + pc)) xcp stk' loc' pc' xcp'`
  from bisim have pc: "pc \<le> length (compE2 e1)" by(rule bisim1_pc_length_compE2)
  show ?case
  proof(cases "pc < length (compE2 e1)")
    case True
    let ?pre = "compE2 e @ [IfFalse (2 + int (length (compE2 e1)))]"
    from exec have exec': "exec_meth (compP2 P) (?pre @ compE2 e1 @ Goto (1 + int (length (compE2 e2))) # compE2 e2)
     (stack_xlift (length STK) (compxE2 e 0 0) @ shift (length ?pre) (stack_xlift (length STK) (compxE2 e1 0 0) @
      shift (length (compE2 e1)) (stack_xlift (length STK) (compxE2 e2 (Suc 0) 0))))
     h (stk @ STK, loc, length ?pre + pc, xcp) ta h' (stk', loc', pc', xcp')"
      by(simp add: stack_xlift_compxE2 shift_compxE2 add_ac)
    hence "exec_meth (compP2 P) (compE2 e1 @ Goto (1 + int (length (compE2 e2))) # compE2 e2)
      (stack_xlift (length STK) (compxE2 e1 0 0) @ shift (length (compE2 e1)) (stack_xlift (length STK) (compxE2 e2 (Suc 0) 0)))
     h (stk @ STK, loc, pc, xcp) ta h' (stk', loc', pc' - length ?pre, xcp')"
      by(rule exec_meth_drop_xt)(auto simp add: stack_xlift_compxE2)
    hence "?exec e1 stk STK loc pc xcp stk' loc' (pc' - length ?pre) xcp'"
      by(rule exec_meth_take_xt)(rule True)
    from IH[OF this] obtain stk'' where stk': "stk' = stk'' @ STK"
      and exec'': "exec_meth (compP2 P) (compE2 e1) (compxE2 e1 0 0) h (stk, loc, pc, xcp)
      ta h' (stk'', loc', pc' - length ?pre, xcp')" by blast
    from exec'' have "exec_meth (compP2 P) (compE2 e1 @ Goto (1 + int (length (compE2 e2))) # compE2 e2)
      (compxE2 e1 0 0 @ shift (length (compE2 e1)) (compxE2 e2 (Suc 0) 0))
     h (stk, loc, pc, xcp) ta h' (stk'', loc', pc' - length ?pre, xcp')"
      by(rule exec_meth_append_xt)
    hence "exec_meth (compP2 P) (?pre @ compE2 e1 @ Goto (1 + int (length (compE2 e2))) # compE2 e2)
      (compxE2 e 0 0 @ shift (length ?pre) (compxE2 e1 0 0 @ shift (length (compE2 e1)) (compxE2 e2 (Suc 0) 0)))
     h (stk, loc, length ?pre + pc, xcp) ta h' (stk'', loc', length ?pre + (pc' - length ?pre), xcp')"
      by(rule append_exec_meth_xt)(auto)
    moreover from exec' have "pc' \<ge> length ?pre"
      by(rule exec_meth_drop_xt_pc)(auto simp add: stack_xlift_compxE2)
    ultimately show ?thesis using stk'
      by(auto simp add: shift_compxE2 stack_xlift_compxE2 add_ac)
  next
    case False
    with pc have [simp]: "pc = length (compE2 e1)" by simp
    from bisim obtain v where "stk = [v]" "xcp = None"
      by(auto dest: bisim1_pc_length_compE2D)
    with exec show ?thesis by(auto elim!: exec_meth.cases intro!: exec_meth.intros)
  qed
next
  case (bisim1CondElse e2 n e2' xs stk loc pc xcp e e1)
  note IH = `\<And>stk' loc' pc' xcp' STK. ?exec e2 stk STK loc pc xcp stk' loc' pc' xcp'
             \<Longrightarrow> ?concl e2 stk STK loc pc xcp stk' loc' pc' xcp'`
  note exec = `?exec (if (e) e1 else e2) stk STK loc (Suc (Suc (length (compE2 e) + length (compE2 e1) + pc))) xcp stk' loc' pc' xcp'`
  note bisim = `P,e2,n,h \<turnstile> (e2', xs) \<leftrightarrow> (stk, loc, pc, xcp)`
  from bisim have pc: "pc \<le> length (compE2 e2)" by(rule bisim1_pc_length_compE2)

  let ?pre = "compE2 e @ IfFalse (2 + int (length (compE2 e1))) # compE2 e1 @ [Goto (1 + int (length (compE2 e2)))]"
  from exec have exec': "exec_meth (compP2 P) (?pre @ compE2 e2)
    (stack_xlift (length STK) (compxE2 e 0 0 @ compxE2 e1 (Suc (length (compE2 e))) 0) @
     shift (length ?pre) (stack_xlift (length STK) (compxE2 e2 0 0)))
    h (stk @ STK, loc, length ?pre + pc, xcp) ta h' (stk', loc', pc', xcp')"
    by(simp add: stack_xlift_compxE2 shift_compxE2 add_ac)
  hence "?exec e2 stk STK loc pc xcp stk' loc' (pc' - length ?pre) xcp'"
    by(rule exec_meth_drop_xt)(auto simp add: stack_xlift_compxE2 shift_compxEs2 add_ac)
  from IH[OF this] obtain stk'' where stk': "stk' = stk'' @ STK"
    and exec'': "exec_meth (compP2 P) (compE2 e2) (compxE2 e2 0 0) h (stk, loc, pc, xcp)
    ta h' (stk'', loc', pc' - length ?pre, xcp')" by blast
  from exec'' have "exec_meth (compP2 P) (?pre @ compE2 e2)
    ((compxE2 e 0 0 @ compxE2 e1 (Suc (length (compE2 e))) 0) @ shift (length ?pre) (compxE2 e2 0 0))
    h (stk, loc, length ?pre + pc, xcp) ta h' (stk'', loc', length ?pre + (pc' - length ?pre), xcp')"
    by(rule append_exec_meth_xt)(auto)
  moreover from exec' have "pc' \<ge> length ?pre"
    by(rule exec_meth_drop_xt_pc)(auto simp add: stack_xlift_compxE2)
  moreover hence "(Suc (Suc (pc' - Suc (Suc 0)))) = pc'" by simp
  ultimately show ?case using stk'
    by(auto simp add: shift_compxE2 stack_xlift_compxE2 add_ac nat_number)
next
  case (bisim1CondThrow e n a xs stk loc pc e1 e2)
  note bisim = `P,e,n,h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)`
  note IH = `\<And>stk' loc' pc' xcp' STK. ?exec e stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'
             \<Longrightarrow> ?concl e stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'`
  note exec = `?exec (if (e) e1 else e2) stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'`
  from bisim have pc: "pc < length (compE2 e)" by(auto dest: bisim1_ThrowD)
  from exec have "exec_meth (compP2 P) (compE2 e @ IfFalse (2 + int (length (compE2 e1))) # compE2 e1 @ Goto (1 + int (length (compE2 e2))) # compE2 e2)
     (stack_xlift (length STK) (compxE2 e 0 0) @ shift (length (compE2 e)) (stack_xlift (length STK) (compxE2 e1 (Suc 0) 0) @
      stack_xlift (length STK) (compxE2 e2 (Suc (Suc (length (compE2 e1)))) 0)))
     h (stk @ STK, loc, pc, \<lfloor>a\<rfloor>) ta h' (stk', loc', pc', xcp')"
    by(simp add: stack_xlift_compxE2 shift_compxE2 add_ac)
  hence "?exec e stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'"
    by(rule exec_meth_take_xt)(rule pc)
  from IH[OF this] show ?case by auto
next
  case (bisim1While1 c n e xs)
  note IH = `\<And>stk' loc' pc' xcp' STK. ?exec c [] STK xs 0 None stk' loc' pc' xcp'
             \<Longrightarrow> ?concl c [] STK xs 0 None stk' loc' pc' xcp'`
  note exec = `?exec (while (c) e) [] STK xs 0 None stk' loc' pc' xcp'`
  hence "exec_meth (compP2 P) (compE2 c @ IfFalse (int (length (compE2 e)) + 3) # compE2 e @ [Pop, Goto (-2 + (- int (length (compE2 e)) - int (length (compE2 c)))), Push Unit])
     (stack_xlift (length STK) (compxE2 c 0 0) @ shift (length (compE2 c)) (stack_xlift (length STK) (compxE2 e (Suc 0) 0)))
     h ([] @ STK, xs, 0, None) ta h' (stk', loc', pc', xcp')"
    by(simp add: compxE2_size_convs)
  hence "?exec c [] STK xs 0 None stk' loc' pc' xcp'"
    by(rule exec_meth_take_xt) simp
  from IH[OF this] show ?case by auto
next
  case (bisim1While3 c n c' xs stk loc pc xcp e)
  note bisim = `P,c,n,h \<turnstile> (c', xs) \<leftrightarrow> (stk, loc, pc, xcp)`
  note IH = `\<And>stk' loc' pc' xcp' STK. ?exec c stk STK loc pc xcp stk' loc' pc' xcp'
             \<Longrightarrow> ?concl c stk STK loc pc xcp stk' loc' pc' xcp'`
  note exec = `?exec (while (c) e) stk STK loc pc xcp stk' loc' pc' xcp'`
  from bisim have pc: "pc \<le> length (compE2 c)" by(rule bisim1_pc_length_compE2)
  show ?case
  proof(cases "pc < length (compE2 c)")
    case True
    from exec have "exec_meth (compP2 P) (compE2 c @ IfFalse (int (length (compE2 e)) + 3) # compE2 e @ [Pop, Goto (-2 + (- int (length (compE2 e)) - int (length (compE2 c)))), Push Unit])
     (stack_xlift (length STK) (compxE2 c 0 0) @ shift (length (compE2 c)) (stack_xlift (length STK) (compxE2 e (Suc 0) 0)))
      h (stk @ STK, loc, pc, xcp) ta h' (stk', loc', pc', xcp')"
      by(simp add: compxE2_size_convs)
    hence "?exec c stk STK loc pc xcp stk' loc' pc' xcp'"
      by(rule exec_meth_take_xt)(rule True)
    from IH[OF this] show ?thesis by auto
  next
    case False
    with pc have [simp]: "pc = length (compE2 c)" by simp
    from bisim obtain v where "stk = [v]" "xcp = None" by(auto dest: bisim1_pc_length_compE2D)
    with exec show ?thesis by(auto elim!: exec_meth.cases intro!: exec_meth.intros)
  qed
next
  case (bisim1While4 e n e' xs stk loc pc xcp c)
  note bisim = `P,e,n,h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, xcp)`
  note IH = `\<And>stk' loc' pc' xcp' STK. ?exec e stk STK loc pc xcp stk' loc' pc' xcp'
             \<Longrightarrow> ?concl e stk STK loc pc xcp stk' loc' pc' xcp'`
  note exec = `?exec (while (c) e) stk STK loc (Suc (length (compE2 c) + pc)) xcp stk' loc' pc' xcp'`
  from bisim have pc: "pc \<le> length (compE2 e)" by(rule bisim1_pc_length_compE2)
  show ?case
  proof(cases "pc < length (compE2 e)")
    case True
    let ?pre = "compE2 c @ [IfFalse (int (length (compE2 e)) + 3)]"
    from exec have "exec_meth (compP2 P) ((?pre @ compE2 e) @ [Pop, Goto (-2 + (- int (length (compE2 e)) - int (length (compE2 c)))), Push Unit])
                   (stack_xlift (length STK) (compxE2 c 0 0) @ shift (length ?pre) (stack_xlift (length STK) (compxE2 e 0 0)))
                    h (stk @ STK, loc, length ?pre + pc, xcp) ta h' (stk', loc', pc', xcp')"
      by(simp add: compxE2_size_convs)
    hence exec': "exec_meth (compP2 P) (?pre @ compE2 e) (stack_xlift (length STK) (compxE2 c 0 0) @ shift (length ?pre) (stack_xlift (length STK) (compxE2 e 0 0)))
                 h (stk @ STK, loc, length ?pre + pc, xcp) ta h' (stk', loc', pc', xcp')"
      by(rule exec_meth_take)(auto intro: True)
    hence "?exec e stk STK loc pc xcp stk' loc' (pc' - length ?pre) xcp'"
      by(rule exec_meth_drop_xt)(auto simp add: stack_xlift_compxE2)      
    from IH[OF this] obtain stk'' where stk': "stk' = stk'' @ STK"
      and exec'': "exec_meth (compP2 P) (compE2 e) (compxE2 e 0 0) h (stk, loc, pc, xcp) ta h' (stk'', loc', pc' - length ?pre, xcp')" by auto
    from exec'' have "exec_meth (compP2 P) (?pre @ compE2 e) (compxE2 c 0 0 @ shift (length ?pre) (compxE2 e 0 0))
                     h (stk, loc, length ?pre + pc, xcp) ta h' (stk'', loc', length ?pre + (pc' - length ?pre), xcp')"
      by(rule append_exec_meth_xt) auto
    hence "exec_meth (compP2 P) ((?pre @ compE2 e) @ [Pop, Goto (-2 + (- int (length (compE2 e)) - int (length (compE2 c)))), Push Unit])
           (compxE2 c 0 0 @ shift (length ?pre) (compxE2 e 0 0))
           h (stk, loc, length ?pre + pc, xcp) ta h' (stk'', loc', length ?pre + (pc' - length ?pre), xcp')"
      by(rule exec_meth_append)
    moreover from exec' have "pc' \<ge> length ?pre"
     by(rule exec_meth_drop_xt_pc)(auto simp add: stack_xlift_compxE2)
   moreover have "-2 + (- int (length (compE2 e)) - int (length (compE2 c))) = - int (length (compE2 c)) + (-2 - int (length (compE2 e)))" by simp
   ultimately show ?thesis using stk'
     by(auto simp add: shift_compxE2 stack_xlift_compxE2 add_ac)
 next
    case False
    with pc have [simp]: "pc = length (compE2 e)" by simp
    from bisim obtain v where "stk = [v]" "xcp = None" by(auto dest: bisim1_pc_length_compE2D)
    with exec show ?thesis by(auto elim!: exec_meth.cases intro!: exec_meth.intros)
  qed
next
  case (bisim1While6 c n e xs)
  note exec = `?exec (while (c) e) [] STK xs (Suc (Suc (length (compE2 c) + length (compE2 e)))) None stk' loc' pc' xcp'`
  thus ?case by(rule exec_meth.cases)(simp_all, auto intro!: exec_meth.intros)
next
  case (bisim1While7 c n e xs)
  note exec = `?exec (while (c) e) [] STK xs (Suc (Suc (Suc (length (compE2 c) + length (compE2 e))))) None stk' loc' pc' xcp'`
  thus ?case by(rule exec_meth.cases)(simp_all, auto intro!: exec_meth.intros)
next
  case (bisim1WhileThrow1 c n a xs stk loc pc e)
  note bisim = `P,c,n,h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)`
  note IH = `\<And>stk' loc' pc' xcp' STK. ?exec c stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'
             \<Longrightarrow> ?concl c stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'`
  note exec = `?exec (while (c) e) stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'`
  from bisim have pc: "pc < length (compE2 c)" by(auto dest: bisim1_ThrowD)
  from exec have "exec_meth (compP2 P) (compE2 c @ IfFalse (int (length (compE2 e)) + 3) # compE2 e @ [Pop, Goto (-2 + (- int (length (compE2 e)) - int (length (compE2 c)))), Push Unit])
     (stack_xlift (length STK) (compxE2 c 0 0) @ shift (length (compE2 c)) (stack_xlift (length STK) (compxE2 e (Suc 0) 0)))
     h (stk @ STK, loc, pc, \<lfloor>a\<rfloor>) ta h' (stk', loc', pc', xcp')"
    by(simp add: compxE2_size_convs)
  hence "?exec c stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'"
    by(rule exec_meth_take_xt)(rule pc)
  from IH[OF this] show ?case by auto
next
  case (bisim1WhileThrow2 e n a xs stk loc pc c)
  note bisim = `P,e,n,h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)`
  note IH = `\<And>stk' loc' pc' xcp' STK. ?exec e stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'
             \<Longrightarrow> ?concl e stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'`
  note exec = `?exec (while (c) e) stk STK loc (Suc (length (compE2 c) + pc)) \<lfloor>a\<rfloor> stk' loc' pc' xcp'`
  from bisim have pc: "pc < length (compE2 e)" by(auto dest: bisim1_ThrowD)
  let ?pre = "compE2 c @ [IfFalse (int (length (compE2 e)) + 3)]"
  from exec have "exec_meth (compP2 P) ((?pre @ compE2 e) @ [Pop, Goto (-2 + (- int (length (compE2 e)) - int (length (compE2 c)))), Push Unit])
     (stack_xlift (length STK) (compxE2 c 0 0) @ shift (length ?pre) (stack_xlift (length STK) (compxE2 e 0 0)))
    h (stk @ STK, loc, length ?pre + pc, \<lfloor>a\<rfloor>) ta h' (stk', loc', pc', xcp')"
    by(simp add: compxE2_size_convs)
  hence exec': "exec_meth (compP2 P) (?pre @ compE2 e)
    (stack_xlift (length STK) (compxE2 c 0 0) @ shift (length ?pre) (stack_xlift (length STK) (compxE2 e 0 0)))
    h (stk @ STK, loc, (length ?pre + pc), \<lfloor>a\<rfloor>) ta h' (stk', loc', pc', xcp')"
    by(rule exec_meth_take)(auto intro: pc)
  hence "?exec e stk STK loc pc \<lfloor>a\<rfloor> stk' loc' (pc' - length ?pre) xcp'"
    by(rule exec_meth_drop_xt)(auto simp add: stack_xlift_compxE2)      
  from IH[OF this] obtain stk'' where stk': "stk' = stk'' @ STK"
    and exec'': "exec_meth (compP2 P) (compE2 e) (compxE2 e 0 0) h (stk, loc, pc, \<lfloor>a\<rfloor>) ta h' (stk'', loc', pc' - length ?pre, xcp')" by auto
  from exec'' have "exec_meth (compP2 P) (?pre @ compE2 e) (compxE2 c 0 0 @ shift (length ?pre) (compxE2 e 0 0))
    h (stk, loc, length ?pre + pc, \<lfloor>a\<rfloor>) ta h' (stk'', loc', length ?pre + (pc' - length ?pre), xcp')"
    by(rule append_exec_meth_xt) auto
  hence "exec_meth (compP2 P) ((?pre @ compE2 e) @ [Pop, Goto (-2 + (- int (length (compE2 e)) - int (length (compE2 c)))), Push Unit])
    (compxE2 c 0 0 @ shift (length ?pre) (compxE2 e 0 0))
    h (stk, loc, length ?pre + pc, \<lfloor>a\<rfloor>) ta h' (stk'', loc', length ?pre + (pc' - length ?pre), xcp')"
    by(rule exec_meth_append)
  moreover from exec' have "pc' \<ge> length ?pre"
    by(rule exec_meth_drop_xt_pc)(auto simp add: stack_xlift_compxE2)
  moreover have "-2 + (- int (length (compE2 e)) - int (length (compE2 c))) = - int (length (compE2 c)) + (-2 - int (length (compE2 e)))" by simp
  ultimately show ?case using stk'
    by(auto simp add: shift_compxE2 stack_xlift_compxE2 add_ac)
next
  case (bisim1Throw1 e n e' xs stk loc pc xcp)
  note bisim = `P,e,n,h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, xcp)`
  note IH = `\<And>stk' loc' pc' xcp' STK. ?exec e stk STK loc pc xcp stk' loc' pc' xcp'
             \<Longrightarrow> ?concl e stk STK loc pc xcp stk' loc' pc' xcp'`
  note exec = `?exec (throw e) stk STK loc pc xcp stk' loc' pc' xcp'`
  from bisim have pc: "pc \<le> length (compE2 e)" by(rule bisim1_pc_length_compE2)
  show ?case
  proof(cases "pc < length (compE2 e)")
    case True
    with exec have "?exec e stk STK loc pc xcp stk' loc' pc' xcp'" by(auto elim: exec_meth_take)
    from IH[OF this] show ?thesis by auto
  next
    case False
    with pc have [simp]: "pc = length (compE2 e)" by simp
    from bisim obtain v where "stk = [v]" "xcp = None" by(auto dest: bisim1_pc_length_compE2D)
    with exec show ?thesis by(auto elim!: exec_meth.cases intro!: exec_meth.intros split: split_if_asm)
  qed
next
  case bisim1Throw2 thus ?case
    apply(auto elim!:exec_meth.cases intro: exec_meth.intros dest!: match_ex_table_stack_xliftD)
    apply(auto intro: exec_meth.intros dest!: match_ex_table_stack_xliftD intro!: exI)
    apply(auto simp add: le_Suc_eq)
    done
next
  case bisim1ThrowNull thus ?case
    apply(auto elim!:exec_meth.cases intro: exec_meth.intros dest!: match_ex_table_stack_xliftD)
    apply(auto intro: exec_meth.intros dest!: match_ex_table_stack_xliftD intro!: exI)
    apply(auto simp add: le_Suc_eq)
    done
next
  case (bisim1ThrowThrow e n a xs stk loc pc)
  note bisim = `P,e,n,h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)`
  note IH = `\<And>stk' loc' pc' xcp' STK. ?exec e stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'
             \<Longrightarrow> ?concl e stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'`
  note exec = `?exec (throw e) stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'`
  from bisim have pc: "pc < length (compE2 e)" by(auto dest: bisim1_ThrowD)
  with exec have "?exec e stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'"
    by(auto elim: exec_meth_take simp add: compxE2_size_convs)
  from IH[OF this] show ?case by auto
next
  case (bisim1Try e V e' xs stk loc pc xcp e2 C')
  note bisim = `P,e,V,h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, xcp)`
  note IH = `\<And>stk' loc' pc' xcp' STK. ?exec e stk STK loc pc xcp stk' loc' pc' xcp'
             \<Longrightarrow> ?concl e stk STK loc pc xcp stk' loc' pc' xcp'`
  note exec = `?exec (try e catch(C' V) e2) stk STK loc pc xcp stk' loc' pc' xcp'`
  from bisim have pc: "pc \<le> length (compE2 e)" by(rule bisim1_pc_length_compE2)
  show ?case
  proof(cases "pc < length (compE2 e)")
    case True
    from exec have exec': "exec_meth (compP2 P) (compE2 e @ Goto (int (length (compE2 e2)) + 2) # Store V # compE2 e2)
      (stack_xlift (length STK) (compxE2 e 0 0) @  shift (length (compE2 e)) (stack_xlift (length STK) (compxE2 e2 (Suc (Suc 0)) 0)) @ [(0, length (compE2 e), C', Suc (length (compE2 e)), length STK)])
      h (stk @ STK, loc, pc, xcp) ta h' (stk', loc', pc', xcp')"
      by(simp add: compxE2_size_convs)
    show ?thesis
    proof(cases xcp)
      case None
      with exec' True have "?exec e stk STK loc pc xcp stk' loc' pc' xcp'"
	apply -
	apply(erule exec_meth.cases)
	apply(cases "compE2 e ! pc")
	apply(fastsimp simp add: is_Ref_def elim!: is_ArrE intro: exec_meth.intros split: split_if_asm)+
	done
      from IH[OF this] show ?thesis by auto
    next
      case (Some a)
      with exec' have [simp]: "h' = h" "loc' = loc" "xcp' = None" "ta = \<epsilon>"
	by(auto elim: exec_meth.cases)
      show ?thesis
      proof(cases "match_ex_table (compP2 P) (cname_of h a) pc (compxE2 e 0 0)")
	case (Some pcd)
	from exec `xcp = \<lfloor>a\<rfloor>` Some pc
	have stk': "stk' = Addr a # (drop (length stk - snd pcd) stk) @ STK"
	  by(auto elim!: exec_meth.cases simp add: match_ex_table_append split: split_if_asm dest!: match_ex_table_stack_xliftD)
	from exec' `xcp = \<lfloor>a\<rfloor>` Some pc have "exec_meth (compP2 P)
	  (compE2 e) (stack_xlift (length STK) (compxE2 e 0 0)) h (stk @ STK, loc, pc, \<lfloor>a\<rfloor>) \<epsilon> h (Addr a # (drop (length (stk @ STK) - (snd pcd + length STK)) (stk @ STK)), loc, pc', None)"
	  apply -
	  apply(rule exec_meth.intros)
	  apply(auto elim!: exec_meth.cases simp add: match_ex_table_append split: split_if_asm dest!: match_ex_table_shift_pcD match_ex_table_stack_xliftD)
	  done
	from IH[unfolded `ta = \<epsilon>` `xcp = \<lfloor>a\<rfloor>` `h' = h`, OF this]
	have stk: "Addr a # drop (length stk - snd pcd) (stk @ STK) = Addr a # drop (length stk - snd pcd) stk @ STK"
	  and exec'': "exec_meth (compP2 P) (compE2 e) (compxE2 e 0 0) h (stk, loc, pc, \<lfloor>a\<rfloor>) \<epsilon> h (Addr a # drop (length stk - snd pcd) stk, loc, pc', None)" by auto
	thus ?thesis using Some stk' `xcp = \<lfloor>a\<rfloor>` by(auto)
      next
	case None
	with Some exec pc have stk': "stk' = Addr a # STK"
	  and pc': "pc' = Suc (length (compE2 e))"
	  and subcls: "compP2 P \<turnstile> cname_of h a \<preceq>\<^sup>* C'"
	  by(auto elim!: exec_meth.cases split: split_if_asm simp add: match_ex_table_append_not_pcs)(simp add: matches_ex_entry_def)
	moreover from Some True None pc' subcls
	have "exec_meth (compP2 P) (compE2 (try e catch(C' V) e2)) (compxE2 (try e catch(C' V) e2) 0 0) h
	  (stk, loc, pc, \<lfloor>a\<rfloor>) \<epsilon> h (Addr a # drop (length stk - 0) stk, loc, pc', None)"
	  by -(rule exec_catch,auto simp add: match_ex_table_append_not_pcs matches_ex_entry_def)
	ultimately show ?thesis using Some by auto
      qed
    qed
  next
    case False
    with pc have [simp]: "pc = length (compE2 e)" by simp
    from bisim obtain v where "stk = [v]" "xcp = None" by(auto dest: bisim1_pc_length_compE2D)
    with exec show ?thesis by(auto elim!: exec_meth.cases intro!: exec_meth.intros split: split_if_asm)
  qed
next
  case bisim1TryCatch1 thus ?case
    by(auto elim!: exec_meth.cases intro!: exec_meth.intros split: split_if_asm)
next
  case (bisim1TryCatch2 e2 V e' xs stk loc pc xcp e C')
  note bisim = `P,e2,Suc V,h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, xcp)`
  note IH = `\<And>stk' loc' pc' xcp' STK. ?exec e2 stk STK loc pc xcp stk' loc' pc' xcp'
             \<Longrightarrow> ?concl e2 stk STK loc pc xcp stk' loc' pc' xcp'`
  note exec = `?exec (try e catch(C' V) e2) stk STK loc (Suc (Suc (length (compE2 e) + pc))) xcp stk' loc' pc' xcp'`
  let ?pre = "compE2 e @ [Goto (int (length (compE2 e2)) + 2), Store V]"
  from exec have exec': "exec_meth (compP2 P) (?pre @ compE2 e2)
    (stack_xlift (length STK) (compxE2 e 0 0) @ shift (length ?pre) (stack_xlift (length STK) (compxE2 e2 0 0)))
    h (stk @ STK, loc, length ?pre + pc, xcp) ta h' (stk', loc', pc', xcp')"
  proof(cases)
    case (exec_catch ha xcp'' PC pc'' d stk'' loc'')
    hence s: "stk' = Addr xcp'' # drop (length stk'' - d) stk''" "stk'' = stk @ STK" "loc' = loc''"
      "pc' = pc''" "ta = \<epsilon>" "h' = ha" "xcp' = None" "xcp = \<lfloor>xcp''\<rfloor>" "h = ha" "loc = loc''"
      "PC = Suc (Suc (length (compE2 e) + pc))" by simp_all
    from `match_ex_table (compP2 P) (cname_of ha xcp'') PC (stack_xlift (length STK) (compxE2 (try e catch(C' V) e2) 0 0)) = \<lfloor>(pc'', d)\<rfloor>` `d \<le> length stk''`
    show ?thesis unfolding s
      by -(rule exec_meth.exec_catch, simp_all add: shift_compxE2 stack_xlift_compxE2, simp add: match_ex_table_append add: matches_ex_entry_def)
  qed(auto intro: exec_meth.intros simp add: shift_compxE2 stack_xlift_compxE2)
  hence "?exec e2 stk STK loc pc xcp stk' loc' (pc' - length ?pre) xcp'"
    by(rule exec_meth_drop_xt)(auto simp add: stack_xlift_compxE2)
  from IH[OF this] obtain stk'' where stk': "stk' = stk'' @ STK"
    and exec'': "exec_meth (compP2 P) (compE2 e2) (compxE2 e2 0 0) h (stk, loc, pc, xcp) ta h' (stk'', loc', pc' - length ?pre, xcp')" by auto
  from exec'' have "exec_meth (compP2 P) (?pre @ compE2 e2) (compxE2 e 0 0 @ shift (length ?pre) (compxE2 e2 0 0)) h (stk, loc, length ?pre + pc, xcp) ta h' (stk'', loc', length ?pre + (pc' - length ?pre), xcp')"
    by(rule append_exec_meth_xt) auto
  hence "exec_meth (compP2 P) (?pre @ compE2 e2) (compxE2 e 0 0 @ shift (length ?pre) (compxE2 e2 0 0) @ [(0, length (compE2 e), C', Suc (length (compE2 e)), 0)]) h (stk, loc, length ?pre + pc, xcp) ta h' (stk'', loc', length ?pre + (pc' - length ?pre), xcp')"
    by(rule exec_meth.cases)(auto intro: exec_meth.intros simp add: match_ex_table_append_not_pcs)
  moreover from exec' have "pc' \<ge> length ?pre"
    by(rule exec_meth_drop_xt_pc)(auto simp add: stack_xlift_compxE2)
  moreover hence "(Suc (Suc (pc' - Suc (Suc 0)))) = pc'" by simp
  ultimately show ?case using stk' by(auto simp add: shift_compxE2 nat_number)
next
  case (bisim1TryFail e V a xs stk loc pc C' fs C'' e2)
  note bisim = `P,e,V,h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)`
  note exec = `?exec (try e catch(C'' V) e2) stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'`
  note a = `h a = \<lfloor>Obj C' fs\<rfloor>` `\<not> P \<turnstile> C' \<preceq>\<^sup>* C''`
  from bisim have "match_ex_table (compP2 P) (cname_of h a) (0 + pc) (compxE2 e 0 0) = None"
    unfolding compP2_def by(rule bisim1_xcp_Some_not_caught)
  moreover from bisim have "pc < length (compE2 e)" by(auto dest: bisim1_ThrowD)
  ultimately have False using exec a
    apply(auto elim!: exec_meth.cases simp add: outside_pcs_compxE2_not_matches_entry outside_pcs_not_matches_entry split: split_if_asm)
    apply(auto simp add: compP2_def match_ex_entry match_ex_table_append_not_pcs)
    done
  thus ?case ..
next
  case (bisim1TryCatchThrow e2 V a xs stk loc pc e C')
  note bisim = `P,e2,Suc V,h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)`
  note IH = `\<And>stk' loc' pc' xcp' STK. ?exec e2 stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'
             \<Longrightarrow> ?concl e2 stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'`
  note exec = `?exec (try e catch(C' V) e2) stk STK loc (Suc (Suc (length (compE2 e) + pc))) \<lfloor>a\<rfloor> stk' loc' pc' xcp'`
  from bisim have pc: "pc < length (compE2 e2)" by(auto dest: bisim1_ThrowD)
  let ?pre = "compE2 e @ [Goto (int (length (compE2 e2)) + 2), Store V]"
  from exec have exec': "exec_meth (compP2 P) (?pre @ compE2 e2) (stack_xlift (length STK) (compxE2 e 0 0) @
    shift (length ?pre) (stack_xlift (length STK)  (compxE2 e2 0 0)))
    h (stk @ STK, loc, length ?pre + pc, \<lfloor>a\<rfloor>) ta h' (stk', loc', pc', xcp')"
  proof(cases)
    case (exec_catch ha xcp'' PC pc'' d stk'' loc'')
    hence s: "stk' = Addr xcp'' # drop (length stk'' - d) stk''" "stk'' = stk @ STK" "loc' = loc''" "pc' = pc''"
      "ta = \<epsilon>" "h' = ha" "xcp' = None" "a = xcp''" "h = ha" "loc = loc''" "PC = Suc (Suc (length (compE2 e) + pc))" by simp_all
    from `match_ex_table (compP2 P) (cname_of ha xcp'') PC (stack_xlift (length STK) (compxE2 (try e catch(C' V) e2) 0 0)) = \<lfloor>(pc'', d)\<rfloor>` `d \<le> length stk''`
    show ?thesis unfolding s
      by -(rule exec_meth.exec_catch, simp_all add: shift_compxE2 stack_xlift_compxE2, simp add: match_ex_table_append add: matches_ex_entry_def)
  qed simp_all
  hence "?exec e2 stk STK loc pc \<lfloor>a\<rfloor> stk' loc' (pc' - length ?pre) xcp'"
    by(rule exec_meth_drop_xt)(auto simp add: stack_xlift_compxE2)
  from IH[OF this] obtain stk'' where stk': "stk' = stk'' @ STK"
    and exec'': "exec_meth (compP2 P) (compE2 e2) (compxE2 e2 0 0) h (stk, loc, pc, \<lfloor>a\<rfloor>) ta h' (stk'', loc', pc' - length ?pre, xcp')" by auto
  from exec'' have "exec_meth (compP2 P) (?pre @ compE2 e2) (compxE2 e 0 0 @ shift (length ?pre) (compxE2 e2 0 0)) h (stk, loc, length ?pre + pc, \<lfloor>a\<rfloor>) ta h' (stk'', loc', length ?pre + (pc' - length ?pre), xcp')"
    by(rule append_exec_meth_xt) auto
  hence "exec_meth (compP2 P) (?pre @ compE2 e2) (compxE2 e 0 0 @ shift (length ?pre) (compxE2 e2 0 0) @ [(0, length (compE2 e), C', Suc (length (compE2 e)), 0)]) h (stk, loc, length ?pre + pc, \<lfloor>a\<rfloor>) ta h' (stk'', loc', length ?pre + (pc' - length ?pre), xcp')"
    by(rule exec_meth.cases)(auto intro!: exec_meth.intros simp add: match_ex_table_append_not_pcs)
  moreover from exec' have "pc' \<ge> length ?pre"
    by(rule exec_meth_drop_xt_pc)(auto simp add: stack_xlift_compxE2)
  moreover hence "(Suc (Suc (pc' - Suc (Suc 0)))) = pc'" by simp
  ultimately show ?case using stk' by(auto simp add: shift_compxE2 nat_number)
next
  case bisims1Nil thus ?case by(auto elim: exec_meth.cases)
next
  case (bisims1List1 e n e' xs stk loc pc xcp es)
  note bisim1 = `P,e,n,h \<turnstile> (e', xs ) \<leftrightarrow> (stk, loc, pc, xcp)`
  note IH1 = `\<And>stk' loc' pc' xcp' STK. ?exec e stk STK loc pc xcp stk' loc' pc' xcp'
              \<Longrightarrow> ?concl e stk STK loc pc xcp stk' loc' pc' xcp'`
  note IH2 = `\<And>xs stk' loc' pc' xcp' STK. ?execs es [] STK xs 0 None stk' loc' pc' xcp'
             \<Longrightarrow> ?concls es [] STK xs 0 None stk' loc' pc' xcp'`
  note exec = `?execs (e # es) stk STK loc pc xcp stk' loc' pc' xcp'`
  from bisim1 have pc: "pc \<le> length (compE2 e)" by(rule bisim1_pc_length_compE2)
  show ?case
  proof(cases "pc < length (compE2 e)")
    case True
    with exec have "?exec e stk STK loc pc xcp stk' loc' pc' xcp'"
      by(simp add: compxEs2_size_convs)(erule exec_meth_take_xt)
    from IH1[OF this] show ?thesis by auto
  next
    case False
    with pc have pc: "pc = length (compE2 e)" by simp
    with bisim1 obtain v where s: "stk = [v]" "xcp = None" by(auto dest: bisim1_pc_length_compE2D)
    with exec pc have exec': "exec_meth (compP2 P) (compE2 e @ compEs2 es)
      (stack_xlift (length STK) (compxE2 e 0 0) @ shift (length (compE2 e)) (stack_xlift (length (v # STK)) (compxEs2 es 0 0)))
      h ([] @ v # STK, loc, length (compE2 e) + 0, None) ta h' (stk', loc', pc', xcp')"
      by(simp add: compxEs2_size_convs compxEs2_stack_xlift_convs)
    hence "?execs es [] (v # STK) loc 0 None stk' loc' (pc' - length (compE2 e)) xcp'"
      by(rule exec_meth_drop_xt)(auto simp add: stack_xlift_compxE2)
    from IH2[OF this] obtain stk'' where stk': "stk' = stk'' @ v # STK"
      and exec'': "exec_meth (compP2 P) (compEs2 es) (compxEs2 es 0 0) h ([], loc, 0, None) ta h' (stk'', loc', pc' - length (compE2 e), xcp')" by auto
    from exec'' have "exec_meth (compP2 P) (compEs2 es) (stack_xlift (length [v]) (compxEs2 es 0 0)) h ([] @ [v], loc, 0, None) ta h' (stk'' @ [v], loc', pc' - length (compE2 e), xcp')"
      by(rule exec_meth_stk_offer)
    hence "exec_meth (compP2 P) (compE2 e @ compEs2 es) (compxE2 e 0 0 @ shift (length (compE2 e)) (stack_xlift (length [v]) (compxEs2 es 0 0))) h ([] @ [v], loc, length (compE2 e) + 0, None) ta h' (stk'' @ [v], loc', length (compE2 e) + (pc' - length (compE2 e)), xcp')"
      by(rule append_exec_meth_xt) auto
    moreover from exec' have "pc' \<ge> length (compE2 e)"
      by(rule exec_meth_drop_xt_pc)(auto simp add: stack_xlift_compxE2)
    ultimately show ?thesis using s pc stk' by(auto simp add: shift_compxEs2 stack_xlift_compxEs2)
  qed
next
  case (bisims1List2 es n es' xs stk loc pc xcp e v)
  note bisim = `P,es,n,h \<turnstile> (es',xs) [\<leftrightarrow>] (stk,loc,pc,xcp)`
  note IH = `\<And>stk' loc' pc' xcp' STK. ?execs es stk STK loc pc xcp stk' loc' pc' xcp'
             \<Longrightarrow> ?concls es stk STK loc pc xcp stk' loc' pc' xcp'`
  note exec = `?execs (e # es) (stk @ [v]) STK loc (length (compE2 e) + pc) xcp stk' loc' pc' xcp'`
  from exec have exec': "exec_meth (compP2 P) (compE2 e @ compEs2 es)
     (stack_xlift (length STK) (compxE2 e 0 0) @ shift (length (compE2 e)) (stack_xlift (length (v # STK)) (compxEs2 es 0 0)))
     h (stk @ v # STK, loc, length (compE2 e) + pc, xcp) ta h' (stk', loc', pc', xcp')"
    by(simp add: compxEs2_size_convs compxEs2_stack_xlift_convs)
  hence "?execs es stk (v # STK) loc pc xcp stk' loc' (pc' - length (compE2 e)) xcp'"
    by(rule exec_meth_drop_xt)(auto simp add: stack_xlift_compxE2)
  from IH[OF this] obtain stk'' where stk': "stk' = stk'' @ v # STK"
    and exec'': "exec_meth (compP2 P) (compEs2 es) (compxEs2 es 0 0) h (stk, loc, pc, xcp) ta h' (stk'', loc', pc' - length (compE2 e), xcp')" by auto
  from exec'' have "exec_meth (compP2 P) (compEs2 es) (stack_xlift (length [v]) (compxEs2 es 0 0)) h (stk @ [v], loc, pc, xcp) ta h' (stk'' @ [v], loc', pc' - length (compE2 e), xcp')"
    by(rule exec_meth_stk_offer)
  hence "exec_meth (compP2 P) (compE2 e @ compEs2 es) (compxE2 e 0 0 @ shift (length (compE2 e)) (stack_xlift (length [v]) (compxEs2 es 0 0))) h (stk @ [v], loc, length (compE2 e) + pc, xcp) ta h' (stk'' @ [v], loc', length (compE2 e) + (pc' - length (compE2 e)), xcp')"
    by(rule append_exec_meth_xt) auto
  moreover from exec' have "pc' \<ge> length (compE2 e)"
    by(rule exec_meth_drop_xt_pc)(auto simp add: stack_xlift_compxE2)
  ultimately show ?case using stk' by(auto simp add: shift_compxEs2 stack_xlift_compxEs2)
next
  case (bisim1Sync12 e1 V e2 xs v)
  note exec = `?exec (sync\<^bsub>V\<^esub> (e1) e2) [Null, v] STK xs (4 + length (compE2 e1) + length (compE2 e2)) \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor> stk' loc' pc' xcp'`
  thus ?case by(auto elim!: exec_meth.cases split: split_if_asm simp add: match_ex_table_append_not_pcs)(simp add: matches_ex_entry_def)
next
  case (bisim1Sync13 e1 V e2 xs v' v)
  note exec = `?exec (sync\<^bsub>V\<^esub> (e1) e2) [v', v] STK xs (4 + length (compE2 e1) + length (compE2 e2)) \<lfloor>addr_of_sys_xcpt IllegalMonitorState\<rfloor> stk' loc' pc' xcp'`
  thus ?case by(auto elim!: exec_meth.cases split: split_if_asm simp add: match_ex_table_append_not_pcs)(simp add: matches_ex_entry_def)
next
  case (bisim1Sync14 e1 V e2 xs v a')
  note exec = `?exec (sync\<^bsub>V\<^esub> (e1) e2) [v, Addr a'] STK xs (7 + length (compE2 e1) + length (compE2 e2)) \<lfloor>addr_of_sys_xcpt IllegalMonitorState\<rfloor> stk' loc' pc' xcp'`
  thus ?case by(auto elim!: exec_meth.cases split: split_if_asm simp add: match_ex_table_append_not_pcs)(simp add: matches_ex_entry_def)
next
  case (bisim1Sync15 e1 V e2 xs a')
  note exec = `?exec (sync\<^bsub>V\<^esub> (e1) e2) [Null, Addr a'] STK xs (7 + length (compE2 e1) + length (compE2 e2)) \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor> stk' loc' pc' xcp'`
  thus ?case by(auto elim!: exec_meth.cases split: split_if_asm simp add: match_ex_table_append_not_pcs)(simp add: matches_ex_entry_def)
qed

lemma bisim1_length_compE2_WTrt_eq:
  "\<lbrakk> P,e,n,h \<turnstile> (e', xs) \<leftrightarrow> ([v], loc, length (compE2 e), None); P,Env,h \<turnstile>1 e' : T \<rbrakk> \<Longrightarrow> P,Env,h \<turnstile>1 Val v : T"
  
  and bisims1_length_compEs2_WTrt_eq:
  "\<lbrakk> P,es,n,h \<turnstile> (es', xs) [\<leftrightarrow>] (rev vs,loc,length (compEs2 es),None); P,Env,h \<turnstile>1 es' [:] Ts \<rbrakk>
  \<Longrightarrow> P,Env,h \<turnstile>1 map Val vs [:] Ts"
proof(induct e n e' xs stk\<equiv>"[v]" loc pc\<equiv>"length (compE2 e)"  xcp\<equiv>"None::addr option"
         and es n es' xs stk\<equiv>"rev vs" loc pc\<equiv>"length (compEs2 es)"  xcp\<equiv>"None::addr option"
   arbitrary: Env T v and Env Ts vs rule: bisim1_bisims1_inducts_split)
  case bisims1List1 thus ?case
    by(clarsimp)(frule bisim1_pc_length_compE2, fastsimp dest: bisim1_pc_length_compE2D)
next
  case bisims1List2 thus ?case
    by(cases vs) auto
qed(fastsimp dest: bisim1_pc_length_compE2 bisims1_pc_length_compEs2)+

lemma bisim_Val_Suc0_conv:
  "P,Val v,n,h \<turnstile> (e, xs) \<leftrightarrow> (stk, loc, Suc 0, xcp) \<longleftrightarrow> (\<exists>v'. e = Val v' \<and> stk = [v'] \<and> loc = xs \<and> xcp = None)"
  (is "?lhs \<longleftrightarrow> (\<exists>v'. ?rhs v')")
proof
  assume ?lhs thus "\<exists>v'. ?rhs v'"
    by-(ind_cases "P,Val v,n,h \<turnstile> (e, xs) \<leftrightarrow> (stk, loc, Suc 0, xcp)", auto)
next
  assume "\<exists>v'. ?rhs v'"
  then obtain v' where "?rhs v'" ..
  moreover have "P,Val v,n,h \<turnstile> (Val v', xs) \<leftrightarrow> ([v'], xs, length (compE2 (Val v)), None)"
    by(rule bisim1Val2) auto
  ultimately show ?lhs by simp
qed

fun wbisim1 :: "J1_prog \<Rightarrow> (((expr1 \<times> locals1) \<times> (expr1 \<times> locals1) list) \<times> heap, (addr option \<times> frame list) \<times> heap) bisim"
where "wbisim1 P ((ex, exs), h) ((xcp, frs), h') \<longleftrightarrow> h = h' \<and> bisim1_list1 P h ex exs xcp frs"

lemma ta_bisim12_extTA2J1_extTA2JVM:
  assumes wf: "wf_J1_prog P"
  and nt: "\<And>n T C M a h. \<lbrakk> n < length \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>; \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> ! n = NewThread T (C, M, a) h \<rbrakk> \<Longrightarrow> (\<exists>fs. h a = \<lfloor>Obj C fs\<rfloor>) \<and> (\<exists>T meth D. P \<turnstile> C sees M:[]\<rightarrow>T =meth in D) \<and> P \<turnstile> h \<surd>"
  shows "ta_bisim (wbisim1 P) (extTA2J1 P ta) (extTA2JVM (compP2 P) ta)"
proof -
  { fix n t C M a m
    assume "n < length \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>" and "\<lbrace>ta\<rbrace>\<^bsub>t\<^esub> ! n = NewThread t (C, M, a) m"
    from nt[OF this] obtain fs T meth D
      where ma: "m a = \<lfloor>Obj C fs\<rfloor>"
      and sees: "P \<turnstile> C sees M: []\<rightarrow>T = meth in D"
      and mconf: "P \<turnstile> m \<surd>" by auto
    from sees_method_compP[OF sees, where f=compMb2]
    have sees': "compP2 P \<turnstile> C sees M: []\<rightarrow>T = (max_stack meth, max_vars meth, compE2 meth @ [Return], compxE2 meth 0 0) in D"
      by(simp add: compMb2_def compP2_def)
    have "bisim1_list1 P m (meth, Addr a # replicate (max_vars meth) arbitrary) [(addr a\<bullet>M([]), [])] None [([], Addr a # replicate (max_vars meth) arbitrary, D, M, 0)]"
    proof
      have "bisim1_list P m D M 0 [(addr a\<bullet>M(map Val []), [])] []"
	by(rule bl1_Nil) simp
      thus "bisim1_list P m D M (length []) [(addr a\<bullet>M([]), [])] []" by simp
      from sees show "P \<turnstile> D sees M: []\<rightarrow>T = meth in D" by(rule sees_method_idemp)
      from sees_wf_mdecl[OF wf sees] obtain T'
	where wt: "P,[Class D] \<turnstile>1 meth :: T'" and sync: "syncvars meth"
	and sub: "P \<turnstile> T' \<le> T" and D: "\<D> meth \<lfloor>{0}\<rfloor>" and B: "\<B> meth (Suc 0)"
	by(auto simp add: wf_mdecl_def)
      from WT1_expr_locks[OF wt] B WT1_noRetBlock[OF wt] have "bsok meth (Suc 0)" by(simp add: bsok_def)
      thus "P,blocks1 (Suc 0) [] meth,Suc 0,m \<turnstile> (meth, Addr a # replicate (max_vars meth) arbitrary) \<leftrightarrow> ([],Addr a # replicate (max_vars meth) arbitrary, 0, None)" by(auto intro: bisim1_refl)
      from WT1_imp_WTrt1[OF wt] sub
      show "exsconf P m T (meth, Addr a # replicate (max_vars meth) arbitrary)"
      proof(rule exsconf.intros)
	from WT1_fv[OF wt] B sync have "fv meth \<subseteq> {0..<Suc 0}" by simp
	with D_D1[OF B sync D] show "\<D>1 (Suc 0) meth \<lfloor>{0}\<rfloor>" by simp
	from ma sees_method_decl_above[OF sees]
	show "P,m,{0} \<turnstile>1 Addr a # replicate (max_vars meth) arbitrary (:\<le>) Class D # env_exp meth"
	  by(simp add: lconf1_def conf_def)
      qed(simp_all add: B)
    qed(rule mconf)
    with sees sees' have "bisim1_list1 P m (snd (snd (snd (method P C M))), Addr a # replicate (max_vars (snd (snd (snd (method P C M))))) arbitrary) [(addr a\<bullet>M([]), [])] None [([], Addr a # replicate (fst (snd (snd (snd (snd (method (compP2 P) C M)))))) arbitrary, fst (method (compP2 P) C M), M, 0)]" by simp }
  thus ?thesis
    apply(auto simp add: ta_bisim_def intro!: list_all2_all_nthI)
    apply(case_tac "\<lbrace>ta\<rbrace>\<^bsub>t\<^esub> ! n", auto simp add: extNTA2JVM_def)
    done
qed

lemma red_external_ta_bisim21: 
  "\<lbrakk> wf_J1_prog P; P \<turnstile> \<langle>a\<bullet>M(vs), h\<rangle> -ta\<rightarrow>ext \<langle>va, h'\<rangle>; h a \<noteq> None; P \<turnstile> h' \<surd> \<rbrakk>
  \<Longrightarrow> ta_bisim (wbisim1 P) (extTA2J1 P ta) (extTA2JVM (compP2 P) ta)"
apply(rule ta_bisim12_extTA2J1_extTA2JVM, assumption)
apply(frule (1) red_external_new_thread_sees)
  apply(fastsimp simp add: in_set_conv_nth)
 apply assumption
apply(frule red_ext_new_thread_heap)
 apply(fastsimp simp add: in_set_conv_nth)
apply simp
done

end