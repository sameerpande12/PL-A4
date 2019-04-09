open A1
exception Not_implemented
exception TypeException
exception IntersectionException
module VarSet = Set.Make(String);;
(* hastype : ((string * exptype) list) -> exptree -> exptype -> bool *)
let rec getVarType g x = match g with
    [] -> raise TypeException
  | g1::g2 -> if(fst g1 = x )then snd g1 else getVarType g2 x
        (*searches the varialbe with string x in the table g*)

let rec getType g e  = match e with
    (*returns the type of e. throws TypeExceptions in case of type errors*)
   N(n) -> Tint
  | B(b) -> Tbool
  |    Var(x) ->
    (
      match g with
        g1::g2 ->
        if( (fst g1) = x ) then snd g1
        else getType g2 (Var(x))
      | [] -> raise TypeException

    )

  | Abs(e1) -> if  ( getType g e1 = Tint) then Tint
    else raise TypeException
  | Negative(e1) -> if  ( getType g e1 = Tint) then Tint
    else raise TypeException


  | Not(e1) -> if ( (getType g e1 ) = Tbool) then Tbool
    else raise TypeException

  | Add(e1,e2) ->  if ( ((getType g e1 )=Tint) &&  ((getType g e2 )=Tint) ) then Tint
    else raise TypeException
  | Sub(e1,e2) ->  if ( ((getType g e1 )=Tint) &&  ((getType g e2 )=Tint) ) then Tint
    else raise TypeException
  |Mult(e1,e2) ->  if ( ((getType g e1 )=Tint) &&  ((getType g e2 )=Tint) ) then Tint
    else raise TypeException
  |Div(e1,e2) ->  if ( ((getType g e1 )=Tint) &&  ((getType g e2 )=Tint) ) then Tint
    else raise TypeException
  |Rem(e1,e2) ->  if ( ((getType g e1 )=Tint) &&  ((getType g e2 )=Tint) ) then Tint
    else raise TypeException


  |Conjunction(e1,e2) ->  if ( ((getType g e1 )=Tbool) &&  ((getType g e2 )=Tbool) ) then Tbool
    else raise TypeException

  |Disjunction(e1,e2) ->  if ( ((getType g e1 )=Tbool) &&  ((getType g e2 )=Tbool) ) then Tbool
    else raise TypeException



  |Equals(e1,e2) ->   if ( ((getType g e1 )=Tint) &&  ((getType g e2 )=Tint) ) then Tbool
    else raise TypeException

  |GreaterTE(e1,e2) ->  if ( ((getType g e1 )=Tint) &&  ((getType g e2 )=Tint) ) then Tbool
    else raise TypeException
  |LessTE(e1,e2) -> if ( ((getType g e1 )=Tint) &&  ((getType g e2 )=Tint) ) then Tbool
    else raise TypeException


  |GreaterT(e1,e2) -> if ( ((getType g e1 )=Tint) &&  ((getType g e2 )=Tint) ) then Tbool
    else raise TypeException

  |LessT(e1,e2) -> if ( ((getType g e1 )=Tint) &&  ((getType g e2 )=Tint) ) then Tbool
    else raise TypeException


  |InParen(e1) -> getType g e1
  | IfThenElse(e1,e2,e3) ->
    if( getType g e1  = Tbool) then
      let tau1 = getType g e2 in
      let tau2 = getType g e3 in

      if(tau1 = tau2) then tau1
      else raise TypeException

    else raise TypeException


  | Tuple(n, elist) ->
    if (n = List.length elist)then
      Ttuple(List.map (getType g) elist)(*Please check here before submitting*)

    else raise TypeException
  |Project((i,n),e1) ->
    (match (getType g e1) with
       Ttuple(tlist) ->
       if(List.length tlist <> n) then raise TypeException
       else  (if( i <1 || i>n)then raise TypeException
              else List.nth tlist(i-1)
             )
     | _ -> raise TypeException
    )
  | Let(d,e1) -> getType ((getYield g d)@g) e1
  | FunctionAbstraction(x,e1)->(*assuming x is already added to the table g*)
    let xtype = getVarType g x in
    Tfunc(xtype , getType g e1)

  | FunctionCall(e1,e2) ->
    let type1 = getType g e1 in
    let type2 = getType g e2 in
    (match type1 with
       Tfunc(tau1,tau2) -> if(type2 = tau1) then tau2
       else raise TypeException
     | _ -> raise TypeException
    )

and getYield g d = match d with(*returns the yield obtained by defintion d using table g*)

   Simple(x,e) -> [(x, getType g e)]
  | Sequence( dlist ) ->
    if(dlist = []) then []
    else
      let tau1 = getYield g (List.hd dlist) in
      ( getYield (tau1@g) (Sequence(List.tl dlist)) )@tau1

  | Parallel(dlist)->
    if(dlist = []) then []
    else
      let doesIntersect =
        try
          let xvar = getDefinedVar (VarSet.empty) (Parallel(dlist)) in
          false
        with IntersectionException -> true
      in

      if(doesIntersect)then raise TypeException
      else
        let tau1 = getYield g (List.hd dlist) in
        ( getYield (g) (Sequence(List.tl dlist)) )@tau1

  | Local(d1,d2)->
    let tau1 = getYield g d1 in
    getYield (tau1@g) d2


and getDefinedVar vset d  = match d with(*returns a set of DefinedVariables in d. vset represents the variables defined so far.*)
    Simple(x,e) -> if(VarSet.mem x  vset) then vset
    else  (VarSet.add x vset)
  | Sequence(dlist)->
    List.fold_right  VarSet.union (List.map (getDefinedVar vset) dlist) (VarSet.empty)
  | Parallel(dlist)->
    let defVarSetList =  (List.map (getDefinedVar vset) dlist) in
    let defunion = List.fold_right  VarSet.union (List.map (getDefinedVar vset) dlist) (VarSet.empty) in

    let rec getSetListSize slist = match slist with
        []-> 0
      | s1::s2 -> (VarSet.cardinal s1) + (getSetListSize s2)
    in

    if( (VarSet.cardinal defunion) = (getSetListSize defVarSetList)  ) then
      defunion
    else raise IntersectionException
  | Local(d1,d2)->getDefinedVar vset d2


let rec hastype g e t =(*returns boolean. True if e has type t under type assumption g. False otherwise( false also when TypeExcpetion occurs)*)
  match e with
    FunctionAbstraction(x,e1)->
    ( match t with
        Tfunc(tau1,tau2)->
        hastype ((x,tau1)::g) e1 tau2
      | _ -> false
     )

  | _ ->
  try
    if(getType g e = t) then true
    else false
  with TypeException -> false


let rec findFromList x dump =(*find an element x from list dump. Returns True if found, false if not*)
  match dump with
   []-> false
 | a::b -> if (a=x) then true else findFromList x b

(* yields : ((string * exptype) list) -> definition -> ((string * exptype) list) -> bool *)
let rec yields g d g_dash =(*boolean which determines if definition d yields g_dash under type assumptin g*)

    try
      let g_prime = getYield g d in
      let rec agrees g1 g2 dump = (*performs one sided checking. Checks if all the variables in g1 are in g2 and agree. Dump is used to keep track of all the visited variables*)
        match g1 with
          [] -> true
        | a::b ->
          if( findFromList (fst a) dump) then
            agrees b g2 dump
          else

              try
                if (List.assoc (fst a) g2) = (snd a) then
                  agrees (b) g2 ((fst a)::dump)
                else
                  false
            with Not_found -> false

       in

      (agrees g_prime g_dash [])&&(agrees g_dash g_prime [])
    with TypeException -> false
