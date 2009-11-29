module Test_setup =
struct
  open List;;
  open Big_int;;
  open Ta;;
  
  (* Build tree automaton *)
  let cnv_rule r = match r with 
    (Ta.Rule(q,f,qs)) -> Ta.Rule (big_int_of_int q, big_int_of_int f, map big_int_of_int qs)
  ;;
  
  let createFta initial rules =
    let f1 = fold_left (fun a q -> Ta.htai_add_qi (big_int_of_int q) a) (Ta.htai_empty) initial in
      fold_left (fun a r -> Ta.htai_add_rule (cnv_rule r) a) f1 rules
  ;;
  
  (* Return info about tree automaton *)
  let info h =
    string_of_big_int( Ta.ls_size (Ta.hta_delta h) ) ^ " Rules"
  ;;
  
  (* Tree pretty printer *)
  
  let rec concpad pad l = 
    match l with
      [] -> "" |
      [s] -> s |
      s::ss -> s ^ pad ^ concpad pad ss
  ;;
  
  let rec pretty_tree  n = match n with 
    (Ta.Node(f, [])) -> string_of_big_int f |
    (Ta.Node(f,ts)) -> string_of_big_int f ^ "(" ^ concpad ", " (map pretty_tree ts) ^ ")"
  ;;
  
  let pretty_witness w = match w with
    None -> "none" |
    Some t -> pretty_tree t
  ;;

end;;
