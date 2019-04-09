
type bigint = sign * int list
and sign = Neg | NonNeg

exception DivisionByZero
exception Invalid_intlist (*raised when the list somehow violate the format by containing non 0-9 integers*)
exception InvalidCondition_diff1 (*used to mark conditions which arise unexpectedly according to the description of prerequisites for input to a specific function*)
exception InvalidCondition_diff2
exception InvalidConditioncmp_same_size
exception NegativeInputException(*arises when negative input is given to function which is not expected to take negative input*)

let mk_big_list (sign,l) =
  match l with
    []-> let (a:bigint) = (NonNeg, [0]) in
    a
  |_ -> let (a:bigint) = (sign,l) in
    a

let rec trim l = match l with
  (*Trims the zeros in front of a list with head as msb. If [] then gives 0*)
    [] -> [0]
  | x::xs -> if(x=0)then trim xs
    else l


let rec mk_list m l = (*given integer m :- appends a list l2 (which represents m with msb as head) ahead of l *)(*takes only positive integer*)
  if(m=0)then l
  else mk_list (m/10) ((m mod 10)::l)



let absolute n = if(n<0)then -n else n (* outputs absolute value of n*)

let mk_big n = (*Given integer n makes a bigint out of it*)

  let m = absolute n in
  let l = trim (mk_list m []) in
  let (output:bigint) = if(n<0)then (Neg,l) else (NonNeg,l) in
  output

let rec print_int_list l = match l with (*given an integer in the form of list in defined format(as in statement) returns the integer value *)
    [] -> ""
  | (x::xs)-> if ( x>= 0 && x<=9) then   (string_of_int x) ^(print_int_list (xs))
    else raise (Invalid_intlist)

let print_num (n:bigint) = match n with (*given an bigint n prints the corresponding integer*)
    (Neg, l) -> "-"^print_int_list(l)
  | (NonNeg,l)-> ""^print_int_list(l)

let get_sign (n:bigint) = match n with (*returns the sign of bigint*)
    (Neg, _)->Neg
  |(NonNeg,_)->NonNeg

let getList (n:bigint) = match n with (*gives the list representing the absolute value of integer*)
    (_,l)->l

let baddc x1 x2 c = (*subroutine for addition to compute "sum" digit and carry "digit" given integers to be summed and carry*)
  let sum = (x1 + x2 + c) mod 10 in
  let carry = ((x1 + x2 + c)/10) in
  (sum,carry)


let rec carryprop l1 c = (* assume l1 is reverse order (i.e lsb is head), add a carry c  *)
  match l1 with
    []-> if (c = 0) then [] else [c]
  |x::xs -> let(sum,carry) = baddc 0 x c in
    sum::(carryprop xs carry)

let rec addc l1 l2 c = (* assumes least significant bit is hd , carries out addition of two lists in rev_order l1 and l2, given initial carry c*)
  match l1 with

    [] ->  ( match l2 with   (*if l1 is empty just propagate carry through l2*)
        []-> if c = 0 then []
        else [c]
      | _ -> carryprop l2 c
    )
  |x::xs ->( match l2 with (*if l2 is empty just propagate carry through l1, else compute sum digit and perform computation recursively*)
        [] -> carryprop l1 c
      | y::ys ->
        let (p,q) = baddc x y c in
        p::( addc xs ys q)
    )

let eq m n =
  if ((fst m)<>(fst n)) then
    if( trim (getList m) = [0] && trim (getList n) = [0] ) then true
    else false(*compares the sign of both the bigint*)
  else
    let rec equal_mag l1 l2 = match (l1,l2) with (*checks if both list represent integers eqaul in magnitude*)
        ([],[]) -> true
      | ([],y::ys) -> false
      | (x::xs,[]) -> false
      | (x::xs, y::ys) ->  if(x<>y) then false
        else equal_mag xs ys in
    equal_mag (snd m) (snd n) (*compares the magnitude *)

let rec cmp_same_size l1 l2 = (* assume that MSB is the first elemeent of list*)
  match (l1,l2) with
    ([],[])->0
  |(x::xs,y::ys) -> if(x>y)then 1 else if(x<y)then -1 else cmp_same_size xs ys
  |(_,_)-> raise InvalidConditioncmp_same_size (*since this function assumes l1 and l2 have same size, hence this condition should not arise*)


let bsubc c x y = (* digit-wise subtraction sub routine. Given x y c, peform x -y - c , return a tuple of sum digit and carry digit *)
  let sum  = x-y-c in (*designed purely with the view of two bigint subtraction*)
  let carry = if(sum < 0 )then 1 else 0 in
  let sum = (10 + (x-y-c)mod 10) mod 10 in
  (sum ,carry)

let rec difflist c l1 l2 = (*assumes l1 represents number strictly greater than l2*) (*lists are in rev_order i.e lsb is the head*)
  match (l1,l2) with
    (x::xs,[])-> (*in case l2 becomes empty we need to carry out single number subtraction from l1*)
    let (sum,carry) = bsubc c x 0 in
    if(carry = 0) then (sum)::xs (*if carry = 0 then just return sum and remaining list*)
    else sum::(difflist carry xs []) (*otherwise carry out difference recursively*)


  | (x::xs,y::ys) -> (*regular substraction*)
    let (sum,carry) = bsubc c x y in
    sum::(difflist carry xs ys)

  | ([],[]) ->  [0]
  (*since conodition List.rev l1 > List.rev l2 numerically , this situation should not arise.*)
  | ([],y::ys)-> raise InvalidCondition_diff2(*since conodition List.rev l1 > List.rev l2 numerically , this situation should not arise.*)




let rec add (m:bigint) (n:bigint) = (*adds bigints m and n , returns the sum*)
  match (m,n) with
    ( (_,[0]), (_,[0]) ) ->(NonNeg,[0]) (*cases of addtion of zero*)
  | ( (_,[0]) ,_) -> n(*when one of them is zero*)
  | (_,(_,[0]))-> m
  | ((NonNeg,l1),(NonNeg,l2))->
    let l = List.rev ( addc (List.rev l1) (List.rev l2) 0 ) in (*addition of two non negative numbers using addc subrouting*)
    ((NonNeg,trim l):bigint)
  | ((Neg,l1),(Neg,l2))->
    let l = List.rev ( addc (List.rev l1) (List.rev l2) 0 ) in (*addition of two positive numbers using addc subrouting, then chaning the sign of the output*)
    ((Neg,trim l):bigint)
  | ((NonNeg,l1),(Neg,l2)) ->    (*When first one is non negative and other is negative *)
    let l1_length = List.length l1 in
    let l2_length = List.length l2 in
    let l1_rev = List.rev l1 in
    let l2_rev = List.rev l2 in
    if(l1_length > l2_length) then (*if l1_length > l2_length then simply abs m > abs n. Hence difflist can be used*)
      (NonNeg,trim (List.rev (difflist 0 l1_rev l2_rev )) )
    else if(l1_length < l2_length) then
      (Neg, trim (getList( add (NonNeg,l2) (Neg,l1) ))) (*in case l1_length < l2_length means abs n > abs m. Hence you can switch the signs temporaritly and use add , then switch back the sign*)

    else
      let comparison = cmp_same_size l1 l2 in (*when size of lists is the same*)
      if(comparison = 0) then (NonNeg,[0]) (*if both are same then return zero*)
      else if(comparison = 1) then
        (NonNeg,trim (List.rev(difflist 0 l1_rev l2_rev)))(*case when l1 > l2 then just compute answer using difflist, set sign as NonNeg. Similar approach for comparision = -1*)
      else(*comparison = -1 means l2 is greater than l1*)
        (Neg,trim  (List.rev (difflist 0 l2_rev l1_rev)))

  | (_,_) -> add n m (*use previosly defined conditions to perform this computation*)

let minus (n:bigint) = match n with
  (*changes the sign of n: bigint*)
    (_,[0]) -> (NonNeg,[0])
  |  (Neg,l) ->  let (answer:bigint) = (NonNeg,l) in answer
  | (NonNeg,l)-> let (answer:bigint) = (Neg,l) in answer

let sub (m:bigint) (n:bigint)= add m (minus n) (*subtraction is just m + (-n)*)

let gt x y = (*compute substraction. If >0 then true else false*)
  let diff = sub x y in
  let (zero:bigint) = (NonNeg,[0]) in

  if((eq diff zero)|| (get_sign(diff) = Neg)) then false
  else true

let lt x y = (*compute substraction. If <0 then true else false*)
  let diff = sub x y in
  let (zero:bigint) = (NonNeg,[0]) in
  if( get_sign(diff)=NonNeg || (eq diff zero) )then false
  else true

let geq x y = not (lt x y) (*not less than*)
let leq x y = not (gt x y) (*not greater than*)

let abs(x:bigint) =
  if(get_sign(x)=Neg)then (NonNeg,getList(x))
  else x

let mult_sign x y = let zero = mk_big 0 in (*gives the sign of output when multiplication of two bigints x and y*)
  if(( eq zero x)||(eq zero y)) then NonNeg
  else if( get_sign(x) = get_sign(y)) then NonNeg
  else Neg

let bmultc c a b = (*multiplication to compute prod and carry digits*)
  let prod = (a*b+c)mod 10 in
  let carry= (a*b + c)/10 in
  (prod,carry)

let rec multiply_prop l y c = (*multiply the list l(assumed in rev_order) by int y and add int c to output*)
  if(y = 0) then [0]
  else (* c is assumed to be positive or zero, x is a digit, l is list of digits in lsb as header*)
    match l with
    |(x::[])-> List.rev (mk_list (x*y + c) [])
    |(x::xs)-> let (prod,carry) = bmultc c x y in
      prod::(multiply_prop xs y carry)
    |([])-> List.rev (mk_list c [])

let rec multiply_list l1 l2 = (* lists with lsb as head assumes c >=0*)
  match (l1,l2) with
    ([],l2)->  []
  | (l1,[]) -> []
  | (x::xs,l2)-> let templist = multiply_prop l2 x 0 in (*initial carry = 0*)
    addc templist (0::(multiply_list xs l2 )) 0 (*multiply by each digit of l2 with appropriate shifts and add*)




let rec mult (x:bigint) (y:bigint)=
  let zero = mk_big 0 in
  if( (eq x zero) || (eq y zero))then zero
  else
    let sign_val = mult_sign x y in
    if(sign_val = Neg) then  minus (mult (minus x) y)
    else
      let xlist = List.rev(getList(x)) and ylist = List.rev(getList(y)) in
      let (answer:bigint) = (sign_val,List.rev( multiply_list xlist ylist )) in
      answer


let rec find_first l1 len = (*returns (front,back,length). front-> first "len" elements if valid or the entire list. Back returns the remaining list. length:- length of front*)
  if(len<0) then raise NegativeInputException
  else if(len = 0) then ([],l1,0)
  else match l1 with
      (x::xs) ->
      let (front,back,length) = find_first xs (len-1) in
      (x::front,back,length+1)
    |([]) -> ([],[],0)




let rec findquotient (m:bigint)  (n:bigint) c= (*assumes l1 > l2 in list format. and quotient between 1 to 9*) (*returns (q, l1-q*l2)*)
  if(c<0) then raise NegativeInputException
  else
    let bigc = mk_big c in
    let temp = sub m (mult n bigc) in
    if(get_sign(temp)=NonNeg) then (c,temp)
    else findquotient m n (c-1)

let rec divide front front_len back back_len l2 l2_len q_revlist =
  if(front_len < l2_len)then (*when the front part is smaller then just attach zero to quotient and move if possible*)
    if( back = [] )then (0::q_revlist,front)
    else divide (front@[(List.hd back)]) (front_len+1) (List.tl back) (back_len-1) l2 l2_len (0::q_revlist)
  else

    let (q, new_front) = findquotient (mk_big_list (NonNeg,front)) (mk_big_list (NonNeg,l2)) 9 in (*attach q to front and move if possible*)
    let new_front = getList(new_front) in
    let new_front_len = List.length new_front in
    if( back = [] )then (q::q_revlist,new_front)
    else
      let new_front_len = if(new_front = [0]) then 0 else new_front_len in
      divide (trim(new_front@[(List.hd back)])) (new_front_len+1) (List.tl back) (back_len-1) l2 l2_len (q::q_revlist)

let  div (m:bigint) (n:bigint) =  (*returns the computed quotient*)
  let (zero:bigint)  = mk_big 0 in
  if(eq n zero) then raise DivisionByZero
  else
    let l1 = getList(m) and l2 = getList(n) in
    let (qlist_rev, remainder) = divide [] 0 l1 (List.length l1) l2 (List.length l2) [] in
    let q_list = trim (List.rev qlist_rev) in

    if(get_sign(m) = get_sign(n)) then
      let (q:bigint) = (NonNeg,q_list) in
      q
    else
      let (q:bigint) = (Neg,q_list) in
      if( eq q zero) then zero
      else q

let  rem (m:bigint) (n:bigint) = (*returns the computed remainder*)
  let (zero:bigint) = mk_big 0 in
  if (eq n zero) then raise DivisionByZero
  else
    let l1 = getList(m) and l2 = getList(n) in
    let rem_list = trim(snd( divide [] 0 l1 (List.length l1) l2 (List.length l2) [] )) in
    let answer = (NonNeg, rem_list) in
    match (get_sign(m),get_sign(n)) with
      (NonNeg,_)-> answer
    | (Neg, _) -> if( (eq answer zero))
      then zero
      else minus answer

(*WE CAN BE SURE THAT ALL mult div add sub minus return (NonNeg,[0]) only when required*)
