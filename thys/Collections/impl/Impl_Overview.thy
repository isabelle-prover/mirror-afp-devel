header {* \isaheader{Overview of Interfaces and Implementations} *}
theory Impl_Overview
imports Main
begin
  text {*
\docIntf{@{text "AnnotatedList"}}{@{text "AnnotatedListSpec"}}
\docAbstype{@{text "('e \<times> 'a::monoid_add) list"}}
\docDesc{Lists with annotated elements. The annotations form a monoid, and there is
  a split operation to split the list according to its annotations. This is the
  abstract concept implemented by finger trees.}
\begin{docImpls}
\docImpl{@{text "FTAnnotatedListImpl"}}
\docType{@{text "('a,'b::monoid_add) ft"}}
\docAbbrv{@{text "ft"}}
\docDesc{Annotated lists implemented by 2-3 finger trees.}
\end{docImpls}
\docIntf{@{text "List"}}{@{text "ListSpec"}}
\docAbstype{@{text "'a list"}}
\docDesc{This interface specifies sequences.}
\begin{docImpls}
\docImpl{@{text "Fifo"}}
\docType{@{text "'a fifo"}}
\docAbbrv{@{text "fifo"}}
\docDesc{Fifo-Queues implemented by two stacks.}
\end{docImpls}
\docIntf{@{text "Map"}}{@{text "MapSpec"}}
\docAbstype{@{text "'k\<rightharpoonup>'v"}}
\docDesc{This interface specifies maps from keys to values.}
\begin{docImpls}
\docImpl{@{text "ArrayHashMap"}}
\docType{@{text "('k,'v) ahm"}}
\docAbbrv{@{text "ahm,a"}}
\docDesc{Array based hash maps without explicit invariant.}
\docImpl{@{text "ArrayMapImpl"}}
\docType{@{text "'v iam"}}
\docAbbrv{@{text "iam,im"}}
\docDesc{Maps of natural numbers implemented by arrays.}
\docImpl{@{text "HashMap"}}
\docType{@{text "'a::hashable hm"}}
\docAbbrv{@{text "hm,h"}}
\docDesc{Hash maps based on red-black trees.}
\docImpl{@{text "ListMapImpl"}}
\docType{@{text "'a lm"}}
\docAbbrv{@{text "lm,l"}}
\docDesc{Maps implemented by associative lists. If you need efficient 
  @{text "insert_dj"} operation, you should use list sets with explicit 
  invariants (lmi).}
\docImpl{@{text "ListMapImpl_Invar"}}
\docType{@{text "'a lmi"}}
\docAbbrv{@{text "lmi,l"}}
\docDesc{Maps implemented by associative lists. Version with explicit 
  invariants that allows for efficient xxx-dj operations.}
\docImpl{@{text "RBTMapImpl"}}
\docType{@{text "('k::linorder,'v) rm"}}
\docAbbrv{@{text "rm,r"}}
\docDesc{Maps over linearly ordered keys implemented by red-black trees.}
\docImpl{@{text "TrieMapImpl"}}
\docType{@{text "('k,'v) tm"}}
\docAbbrv{@{text "tm,t"}}
\docDesc{Maps over keys of type @{typ "'k list"} implemented by tries.}
\end{docImpls}
\docIntf{@{text "Prio"}}{@{text "PrioSpec"}}
\docAbstype{@{text "('e \<times> 'a::linorder) multiset"}}
\docDesc{Priority queues that may contain duplicate elements.}
\begin{docImpls}
\docImpl{@{text "BinoPrioImpl"}}
\docType{@{text "('a,'p::linorder) bino"}}
\docAbbrv{@{text "bino"}}
\docDesc{Binomial heaps.}
\docImpl{@{text "FTPrioImpl"}}
\docType{@{text "('a,'p::linorder) alprioi"}}
\docAbbrv{@{text "alprioi"}}
\docDesc{Priority queues based on 2-3 finger trees.}
\docImpl{@{text "SkewPrioImpl"}}
\docType{@{text "('a,'p::linorder) skew"}}
\docAbbrv{@{text "skew"}}
\docDesc{Priority queues by skew binomial heaps.}
\end{docImpls}
\docIntf{@{text "PrioUnique"}}{@{text "PrioUniqueSpec"}}
\docAbstype{@{text "('e \<rightharpoonup> 'a::linorder)"}}
\docDesc{Priority queues without duplicate elements. This interface defines a
  decrease-key operation.}
\begin{docImpls}
\docImpl{@{text "FTPrioUniqueImpl"}}
\docType{@{text "('a::linorder,'p::linorder) aluprioi"}}
\docAbbrv{@{text "aluprioi"}}
\docDesc{Unique priority queues based on 2-3 finger trees.}
\end{docImpls}
\docIntf{@{text "Set"}}{@{text "SetSpec"}}
\docAbstype{@{text "'a set"}}
\docDesc{Sets}
\begin{docImpls}
\docImpl{@{text "ArrayHashSet"}}
\docType{@{text "('a) ahs"}}
\docAbbrv{@{text "ahs,a"}}
\docDesc{Array based hash sets without explicit invariant.}
\docImpl{@{text "ArraySetImpl"}}
\docType{@{text "ias"}}
\docAbbrv{@{text "ias,is"}}
\docDesc{Sets of natural numbers implemented by arrays.}
\docImpl{@{text "HashSet"}}
\docType{@{text "'a::hashable hs"}}
\docAbbrv{@{text "hs,h"}}
\docDesc{Hash sets based on red-black trees.}
\docImpl{@{text "ListSetImpl"}}
\docType{@{text "'a ls"}}
\docAbbrv{@{text "ls,l"}}
\docDesc{Sets implemented by distinct lists. For efficient 
  @{text "insert_dj"}-operations, use the version with explicit invariant (lsi).}
\docImpl{@{text "ListSetImpl_Invar"}}
\docType{@{text "'a lsi"}}
\docAbbrv{@{text "lsi,l"}}
\docDesc{Sets by lists with distinct elements. Version with explicit invariant that 
  supports efficient @{text "insert_dj"} operation.}
\docImpl{@{text "ListSetImpl_NotDist"}}
\docType{@{text "'a lsnd"}}
\docAbbrv{@{text "lsnd"}}
\docDesc{Sets implemented by lists that may contain duplicate elements. 
  Insertion is quick, but other operations are less performant than on 
  lists with distinct elements.}
\docImpl{@{text "ListSetImpl_Sorted"}}
\docType{@{text "'a::linorder lss"}}
\docAbbrv{@{text "lss"}}
\docDesc{Sets implemented by sorted lists.}
\docImpl{@{text "RBTSetImpl"}}
\docType{@{text "('a::linorder) rs"}}
\docAbbrv{@{text "rs,r"}}
\docDesc{Sets over linearly ordered elements implemented by red-black trees.}
\docImpl{@{text "TrieSetImpl"}}
\docType{@{text "('a) ts"}}
\docAbbrv{@{text "ts,t"}}
\docDesc{Sets of elements of type @{typ "'a list"} implemented by tries.}
\end{docImpls}
  *}
end
