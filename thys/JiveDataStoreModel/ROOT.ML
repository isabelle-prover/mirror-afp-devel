(* $Id: ROOT.ML,v 1.3 2007-08-07 18:30:19 makarius Exp $ *)
(* License: LGPL *)

add_path "Isabelle";
add_path "Isabelle_Store";
add_path "Isa_Counter";
add_path "Isa_Counter_Store";

use_thys [
  "TypeIds",
  "JavaType",
  "DirectSubtypes",
  "Subtype",
  "Attributes",
  "AttributesIndep",
  "Value",
  "Location",
  "Store",
  "StoreProperties",
  "JML",
  "UnivSpec"
];
