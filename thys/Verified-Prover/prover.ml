type pred = int;;

type var = int;;

type form = 
    PAtom of (pred*(var list))
  | NAtom of (pred*(var list))
  | FConj of form * form
  | FDisj of form * form
  | FAll of form
  | FEx of form
;;

let rec preSuc t = match t with
    [] -> []
  | (a::list) -> (match a with 0 -> preSuc list | sucn -> (sucn-1::preSuc list));;

let rec fv t = match t with
    PAtom (p,vs) -> vs
  | NAtom (p,vs) -> vs
  | FConj (f,g) -> (fv f)@(fv g)
  | FDisj (f,g) -> (fv f)@(fv g)
  | FAll f -> preSuc (fv f)
  | FEx f -> preSuc (fv f);;

let suc x = x+1;;

let bump phi n y = match y with 0 -> n | sucn -> suc (phi (sucn-1));;

let map = List.map;;

let rec subst r f = match f with
    PAtom (p,vs) -> PAtom (p,map r vs)
  | NAtom (p,vs) -> NAtom (p,map r vs)
  | FConj (f,g) -> FConj (subst r f, subst r g)
  | FDisj (f,g) -> FDisj (subst r f, subst r g)
  | FAll f -> FAll (subst (bump r 0) f)
  | FEx f -> FEx (subst (bump r 0) f);;

let finst body w = subst (fun v -> match v with 0 -> w | sucn -> (sucn-1)) body;;

type seq = form list;;

type nform = int * form;;

type nseq = nform list;;

let s_of_ns ns = map snd ns;;

let ns_of_s s = map (fun x -> (0,x)) s;;

let flat = List.flatten;;

let sfv s = flat (map fv s);;

let rec maxvar t = match t with
    [] -> 0
  | (a::list) -> max a (maxvar list);;

let newvar vs = suc (maxvar vs);;

let mem = List.mem;;

let rec is_axiom t = match t with
    [] -> false
  | (a::list) -> match a with
	PAtom (p,vs) -> (mem (NAtom (p,vs)) list or is_axiom list)
      | NAtom (p,vs) -> (mem (PAtom (p,vs)) list or is_axiom list)
      | FConj (f,g) -> is_axiom list 
      | FDisj (f,g) -> is_axiom list 
      | FAll f -> is_axiom list
      | FEx f -> is_axiom list;;


let subsf t = match t with 
    [] -> []
  | (x::xs) -> let (m,f) = x in
      match f with 
	  PAtom (p,vs) -> [xs@[(0,PAtom (p,vs))]]
	| NAtom (p,vs) -> [xs@[(0,NAtom (p,vs))]]
	| FConj (f,g)  -> [xs@[(0,f)];xs@[(0,g)]]
	| FDisj (f,g) -> [xs@[(0,f);(0,g)]]
	| FAll f -> [xs@[(0,finst f (newvar (sfv (s_of_ns (x::xs)))))]]
	| FEx f -> [xs@[(0,finst f m);(suc m,FEx f)]];;

let rec iter g a t = match t with
    0 -> a
  | sucn -> g (iter g a (sucn-1));;

let filter = List.filter;;

let fSucn fn = 
  (let fn1 = filter (fun x -> not (is_axiom (s_of_ns x))) fn in
   let fn2 = map subsf fn1 in
   let fn3 = flat fn2 in
     fn3);;

let rec prove' l = (if l = [] then true else (prove' (fSucn l)));;

let prove s = prove' [s];;

let my_f = FDisj (
  (FAll (FConj ((NAtom (0,[0])), (NAtom (1,[0])))),
  (FDisj ((FEx ((PAtom (1,[0])))),(FEx (PAtom (0,[0])))))));;

prove [(0,my_f)];;
