(*  Title:      RSAPSS/SHA1Padding.thy
    ID:         $Id: SHA1Padding.thy,v 1.4 2008-06-12 06:57:26 lsf37 Exp $
    Author:     Christina Lindenberg, Kai Wirt, Technische Universität Darmstadt
    Copyright:  2005 - Technische Universität Darmstadt
*)


header "Message Padding for SHA1"

theory SHA1Padding
imports WordOperations
begin

definition zerocount :: "nat \<Rightarrow> nat" where
  zerocount: "zerocount n = ((((n + 64) div 512) + 1) * 512) - n - (65::nat)"

definition helppadd :: "bv \<Rightarrow> bv \<Rightarrow> nat \<Rightarrow> bv" where
  "helppadd x y n = x @ [One] @ zerolist (zerocount n) @ zerolist (64 - length y) @y"

definition sha1padd :: "bv \<Rightarrow> bv" where
  sha1padd: "sha1padd x = helppadd x (nat_to_bv (length x)) (length x)"

end
